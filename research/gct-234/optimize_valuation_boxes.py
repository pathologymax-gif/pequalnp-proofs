"""Build a kernel-checkable sparse valuation specialization of William Zheng's L-gct-234 proof."""
from pathlib import Path
import argparse
import ast
import re

baseline = Path(__file__).with_name('pr23279.lean').read_text(encoding='utf-8')
rules = {491,493,495,497,499,501}
maskdef = '''private def sparseVal (v : Nat → Int) (one free k : Nat) : Int :=
  if one.testBit k then 1 else if free.testBit k then v k else 0'''
packdef = '''private def ruleConj (pred : Nat → Prop) : List Nat → Prop
  | [] => True
  | k :: more => pred k ∧ ruleConj pred more

private theorem ruleConj_of_mem {pred : Nat → Prop} {indices : List Nat}
    (h : ∀ k ∈ indices, pred k) : ruleConj pred indices := by
  induction indices with
  | nil => trivial
  | cons k more ih =>
    exact ⟨h k (List.mem_cons_self ..), ih (fun n hn => h n (List.mem_cons_of_mem _ hn))⟩
'''


def get_block(marker):
    start = baseline.index(marker)
    return baseline[start:baseline.index('\n\n',start)]


def table_parts(name):
    definition = get_block('private def '+name+' :')
    header = re.search(r'\d+, #(\[[^\]]*\]), (\[[^\]]*\])',definition)
    digits, zeros = map(ast.literal_eval, header.groups())
    fields = r'⟨(\[[^\]]*\]),\s*(\[[^\]]*\]),\s*(\[[^\]]*\]),\s*(\[[^\]]*\]),\s*(\[[^\]]*\])⟩'
    boxes = [tuple(ast.literal_eval(f) for f in group) for group in re.findall(fields,definition)]
    return digits,zeros,boxes


def original_arithmetic(name):
    return get_block('private theorem boxesArithmetic'+name+' :')


def proof(name):
    table='boxTable'+name
    masks='valuationMasks'+name
    digits,zeros,boxes=table_parts(table)
    original=original_arithmetic(name)
    pre,tail=original.split('  all_goals simp [boxTable',1)
    entries=[]
    for row,ones,*_ in boxes:
        if not set(row)<=rules:
            entries.append('(0,0,[])')
            continue
        one=sum(1<<k for k in ones if not digits[k]); free=sum(1<<k for k,d in enumerate(digits) if not d and k not in ones)
        entries.append(f"({one},{free},[{','.join(map(str,row))}])")
    data=f'private def {masks} : Array (Nat × Nat × List Nat) := #[\n  '+',\n  '.join(entries)+']\n\n'
    pre=pre.replace('  have members',f'  let j := i\n  have eqs := ruleConj_of_mem hr\n  simp [{table}, List.forall_mem_cons] at hz\n  have members')
    result=pre+f'''  all_goals
    first
    | (have small : ruleConj (disjointNonTriadRulesLinear (sparseVal v ({masks}[j]!).1 ({masks}[j]!).2.1) m u) ({masks}[j]!).2.2 := by
         simp [j,{masks}]
         exact eqs
       clear eqs hr
       simp [{table}, BoxTable.atBox, List.forall_mem_cons] at hb
       simp (config := {{decide := true}}) [j,{masks},ruleConj,disjointNonTriadRulesLinear,sparseVal] at small
       omega)'''
    if any(not set(b[0])<=rules for b in boxes):
        result+='\n    | skip\n  all_goals clear eqs\n  all_goals simp [boxTable'+tail
    return data,result


def optimize(source,names):
    for name in names:
        data,body=proof(name)
        orig=original_arithmetic(name)
        prefix='set_option maxRecDepth 32768 in\nset_option maxHeartbeats 0 in\n'
        assert prefix+orig in source,name
        source=source.replace(prefix+orig, data+prefix+body,1)
    key='private def valuationMasks'+names[0]
    return source.replace(key,maskdef+'\n\n'+packdef+'\n'+key,1)


if __name__=='__main__':
    p=argparse.ArgumentParser();p.add_argument('source',type=Path);p.add_argument('target',type=Path);p.add_argument('--rows',default='001110');a=p.parse_args()
    src=a.source.read_text(encoding='utf8');new=optimize(src,a.rows.split(','));a.target.write_bytes(new.encode('utf8'))
    print('generated',a.target,'size',a.target.stat().st_size,'bytes')
