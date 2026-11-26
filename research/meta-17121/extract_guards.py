"""Construct the two-sided normal form of a concrete bit-vector circuit."""

from dataclasses import dataclass
from functools import cache


@dataclass(frozen=True)
class Expr:
    op: str
    data: tuple


ZERO = Expr('constant',(0,))
ONE = Expr('constant',(1,))


def gate(op, x, y):
    if x == y:
        return x
    if x in (ZERO,ONE):
        return x if (op=='and')==(x==ZERO) else y
    if y in (ZERO,ONE):
        return y if (op=='and')==(y==ZERO) else x
    return Expr(op,(x,y))


def postorder(roots):
    seen, gates = set(), []
    def visit(node):
        if node in seen:
            return
        seen.add(node)
        if node.op in ('or','and'):
            for p in node.data:
                visit(p)
            gates.append(node)
    for root in roots:
        visit(root)
    return gates


def replace(root, wire, new):
    @cache
    def go(node):
        if node == wire:
            return new
        if node.op in ('or','and'):
            return gate(node.op,*(go(p) for p in node.data))
        return node
    return go(root)


def extract(words, width, trace, output):
    """Return (d,a,b,uses_residual,program,index) in original input numbering.

    Each input instruction is (op,left_index,right_index) in chronological
    order. Program output may select any raw or computed wire.
    """
    mask = (1<<width)-1
    leaves = [ZERO if v==0 else ONE if v==mask else Expr('raw',(i,))
              for i,v in enumerate(words)]
    all_wires = list(leaves)
    for op,x,y in trace:
        if op not in ('and','or') or not (0 <= x < len(all_wires) and 0 <= y < len(all_wires)):
            raise ValueError('Invalid binary program')
        all_wires.append(gate(op,all_wires[x],all_wires[y]))
    if not 0 <= output < len(all_wires):
        raise ValueError('Invalid output')
    root = all_wires[output]
    @cache
    def value(node):
        if node.op=='raw':
            return words[node.data[0]]
        if node.op=='constant':
            return mask if node==ONE else 0
        a,b = map(value,node.data)
        return a & b if node.op=='and' else a | b
    target = value(root)
    def mixed(node):
        v = value(node)
        return bool(v & ~target and target & ~v)
    if target in (0,mask) or any(not mixed(w) for w in leaves if w not in (ZERO,ONE)):
        raise ValueError('The target must be nonconstant and the usable raw signals mixed')
    low, high = [], []
    def compose(rem):
        for term in low:
            rem = gate('or',rem,term)
        for term in high:
            rem = gate('and',rem,term)
        return rem
    capacity = len(postorder([root]))
    while True:
        # Recompute reachability after every substitution to avoid extracting a
        # guard whose sole reader vanished in an earlier simplification.
        first = next((v for v in postorder([root]) if not mixed(v)),None)
        if first is None:
            break
        v = value(first)
        if v in (0,mask):
            c = ZERO if v==0 else ONE
        elif not v & ~target:
            assert first.op=='and'
            low.append(first)
            c = ZERO
        else:
            assert first.op=='or' and not target & ~v
            high.append(first)
            c = ONE
        root = replace(root,first,c)
        assert value(compose(root)) == target
        if root==ZERO:
            high.clear()
        elif root==ONE:
            low.clear()
        current = len(postorder([compose(root)]))
        assert current <= capacity
        capacity = current
    if root==ZERO:
        high.clear()
    elif root==ONE:
        low.clear()
    else:
        assert mixed(root) and low and high
    guards = set(low+high)
    roots = [root]+low+high
    core = [v for v in postorder(roots) if v not in guards]
    assert all(mixed(v) for v in core)
    ordered = core+low+high
    out = compose(root)
    for v in postorder([out]):
        if v not in ordered:
            ordered.append(v)
    # Drop any guards that became structurally redundant in a non-minimum
    # input circuit. The resulting emitted DAG always bounds the original size.
    live = set(postorder([out]))
    ordered = list(dict.fromkeys(v for v in ordered if v in live))
    lookup = {v:i for i,v in enumerate(leaves)}
    result = []
    for v in ordered:
        a,b = (lookup[p] for p in v.data)
        result.append((v.op,a,b))
        lookup[v] = len(words)+len(result)-1
    assert value(out)==target and len(result)<=len(trace)
    return len(set(core)&live),len(set(low)&live),len(set(high)&live),root not in (ZERO,ONE),result,lookup[out]
