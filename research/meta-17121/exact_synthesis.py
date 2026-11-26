"""Bounded AND/OR synthesis on a partial truth table, with witness replay."""
import argparse
from itertools import combinations
import json
from pathlib import Path


class Formula:
    def __init__(self):
        self.nvars = 0
        self.clauses = []

    def var(self):
        self.nvars += 1
        return self.nvars

    def clause(self, *entries):
        # bool is a subclass of int; distinguish constants from literal 1.
        if any(x is True for x in entries):
            return
        lits = tuple(dict.fromkeys(x for x in entries if x is not False))
        if any(-x in lits for x in lits):
            return
        self.clauses.append(lits)

    def selection(self, variables, enabled):
        self.clause(-enabled, *variables)
        for x in variables:
            self.clause(-x, enabled)
        for a,b in combinations(variables,2):
            self.clause(-a,-b)

    def write(self, path):
        with Path(path).open("w",encoding="ascii",newline="\n") as f:
            f.write(f"p cnf {self.nvars} {len(self.clauses)}\n")
            for clause in self.clauses:
                f.write(" ".join(map(str,clause))+" 0\n")


def neg(literal):
    return not literal if isinstance(literal,bool) else -literal


def correct(literal, expected):
    return literal if expected else neg(literal)


def bits(word, sample_ids):
    return [bool((word >> t) & 1) for t in sample_ids]


def samples_for(seeds, target, width):
    seen = {}
    for i in range(width):
        column = tuple((v >> i) & 1 for v in seeds)
        label = (target >> i) & 1
        if column in seen and seen[column][0] != label:
            raise ValueError("Identical sample with inconsistent required outputs")
        if column not in seen:
            seen[column] = (label,i)
    return [i for _,i in seen.values()]


def encode(seeds, target, width, bound, dominance=True, ordered=True):
    if target in seeds or bound < 1:
        raise ValueError("This generator expects a non-seed target and a positive gate bound.")
    indices = [i for i,word in enumerate(seeds) if word]
    sample_ids = samples_for(seeds,target,width)
    labels = bits(target,sample_ids)
    wire_values = [bits(seeds[i],sample_ids) for i in indices]
    n_inputs = len(indices)
    form = Formula()
    live = [form.var() for _ in range(bound)]
    form.clause(live[0])
    for before,after in zip(live,live[1:]):
        form.clause(-after,before)
    left, right, operations = [], [], []

    for g in range(bound):
        n = len(wire_values)
        ls = [form.var() for _ in range(n)]
        rs = [form.var() for _ in range(n)]
        form.selection(ls,live[g])
        form.selection(rs,live[g])
        for i in range(n):
            for j in range(i+1):
                form.clause(-ls[i],-rs[j])
        if ordered and g:
            for i,prev in enumerate(right[-1]):
                for cur in rs[:i]:
                    form.clause(-prev,-cur)

        op = form.var()  # true = AND
        x = [form.var() for _ in labels]
        y = [form.var() for _ in labels]
        z = [form.var() for _ in labels]
        for w,data in enumerate(wire_values):
            for k,source in enumerate(data):
                for select,wire in ((ls[w],x[k]),(rs[w],y[k])):
                    form.clause(-select,-wire,source)
                    form.clause(-select,wire,neg(source))
        for k,(a,b,value) in enumerate(zip(x,y,z)):
            form.clause(-a,-b,value)
            form.clause(a,b,-value)
            form.clause(-op,-value,a)
            form.clause(-op,-value,b)
            form.clause(op,value,-a)
            form.clause(op,value,-b)
            has_next = live[g+1] if g+1<bound else False
            form.clause(-live[g],has_next,correct(value, labels[k]))

        if dominance:
            # An active new word must improve on every earlier word on some
            # sampled bit. The omitted zero wire is still a possible dominator.
            priors = wire_values + ([[False]*len(labels)] if 0 in seeds else [])
            for prior in priors:
                witnesses = []
                for k,old in enumerate(prior):
                    good = correct(z[k],labels[k])
                    bad = neg(correct(old,labels[k]))
                    if bad is True:
                        witnesses.append(good)
                    elif bad is not False:
                        witness = form.var()
                        form.clause(-witness,bad)
                        form.clause(-witness,good)
                        witnesses.append(witness)
                form.clause(-live[g],*witnesses)

        wire_values.append(z)
        left.append(ls)
        right.append(rs)
        operations.append(op)

    # Trim unused active gates; deletion preserves admissibility and only
    # removes potential dominators. Every gate preceding the last has a user.
    for g in range(bound-1):
        output = n_inputs+g
        users = [s[output] for h in range(g+1,bound) for s in (left[h],right[h])]
        form.clause(-live[g+1],*users)
    metadata = dict(seed_indices=indices,seed_words=seeds,target=target,width=width,
                    samples=sample_ids,live=live,left=left,right=right,op=operations,
                    dominance=dominance,ordered=ordered)
    return form,metadata


def dominated(old,new,target):
    return ((old ^ target) & (new ^ target)) == (old ^ target)


def decode(metadata, positive):
    words = metadata["seed_words"][:]
    target = metadata["target"]
    mapped = list(metadata["seed_indices"])
    result = []
    for enable,ls,rs,op in zip(metadata["live"],metadata["left"],
                               metadata["right"],metadata["op"]):
        if enable not in positive:
            break
        a, = [mapped[i] for i,v in enumerate(ls) if v in positive]
        b, = [mapped[i] for i,v in enumerate(rs) if v in positive]
        is_and = op in positive
        value = (words[a] & words[b]) if is_and else (words[a] | words[b])
        match = next((i for i,old in enumerate(words) if dominated(old,value,target)),None)
        if match is None:
            result.append(dict(a=a,b=b,op="and" if is_and else "or",value=value))
            mapped.append(len(words))
            words.append(value)
        else:
            mapped.append(match)
        if target in words:
            break
    if target not in words:
        raise ValueError("Model failed independent bitwise replay")
    check_witness(metadata["seed_words"],target,result,len(metadata["live"]))
    return result


def check_witness(seeds,target,gates,bound):
    if len(gates)>bound:
        raise ValueError("Gate budget exceeded")
    w=seeds[:]
    for g in gates:
        if g["op"] not in ("and","or") or not (0<=g["a"]<len(w) and 0<=g["b"]<len(w)):
            raise ValueError("Invalid gate")
        a,b=w[g["a"]],w[g["b"]]
        v=(a&b) if g["op"]=="and" else (a|b)
        if v!=g["value"] or any(dominated(x,v,target) for x in w):
            raise ValueError("Wrong value or dominated gate")
        w.append(v)
    if target not in w:
        raise ValueError("Target not reached")


def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--case",type=int,choices=range(4),required=True)
    parser.add_argument("--gates",type=int,default=18)
    parser.add_argument("--out",type=Path,required=True)
    parser.add_argument("--no-dominance",action="store_true")
    parser.add_argument("--no-order",action="store_true")
    args=parser.parse_args()
    tables=json.loads(Path(__file__).with_name("seed_tables.json").read_text())
    cnf,meta=encode(tables[args.case],16383,32,args.gates,not args.no_dominance,not args.no_order)
    cnf.write(args.out)
    args.out.with_suffix(".json").write_text(json.dumps(meta),encoding="utf8")
    print(f"case={args.case} gates={args.gates} variables={cnf.nvars} clauses={len(cnf.clauses)}")


if __name__=="__main__":
    main()
