"""Produce the shared sparse valuation proof without storing a second numeric table."""
from pathlib import Path
from optimize_valuation_boxes import original_arithmetic,maskdef,packdef,table_parts,rules
import argparse


list_mask='''private def listBitMask : List Nat → Nat
  | [] => 0
  | k :: ks => 2^k + listBitMask ks

private def sparsifyOrder (c : BoxTable) (i : Nat) (v : Nat → Int) : Nat → Int :=
  let ones := listBitMask (c.atBox i).ones
  sparseVal v ones (listBitMask c.zeros - ones)
'''


def compact_proof(name):
    table='boxTable'+name
    original=original_arithmetic(name)
    pre,tail=original.split('  all_goals simp [boxTable',1)
    pre=pre.replace('  have members',f'  let j := i\n  have eqs := ruleConj_of_mem hr\n  simp [{table}, List.forall_mem_cons] at hz\n  have members')
    fast=pre+f'''  all_goals
    first
    | (have small : ruleConj (disjointNonTriadRulesLinear (sparsifyOrder {table} j v) m u) ({table}.atBox j).rules := by
         norm_num [j, {table}, BoxTable.atBox, sparsifyOrder, listBitMask]
         exact eqs
       clear eqs hr
       simp [{table}, BoxTable.atBox, List.forall_mem_cons] at hb
       norm_num [j,{table},BoxTable.atBox,sparsifyOrder,listBitMask,ruleConj,disjointNonTriadRulesLinear,sparseVal] at small
       simp (config := {{decide := true}}) at small
       omega)'''
    if any(not set(b[0])<=rules for b in table_parts(table)[2]):
        fast+='\n    | skip\n  all_goals clear eqs\n  all_goals simp [boxTable'+tail
    return fast


def replace(source,names):
    for j,name in enumerate(names):
        old=original_arithmetic(name)
        prefix='set_option maxRecDepth 32768 in\nset_option maxHeartbeats 0 in\n'
        helpers=maskdef+'\n\n'+packdef+'\n'+list_mask+'\n' if j==0 else ''
        assert prefix+old in source,name
        source=source.replace(prefix+old,helpers+prefix+compact_proof(name),1)
    return source


if __name__=='__main__':
    p=argparse.ArgumentParser()
    p.add_argument('source',type=Path)
    p.add_argument('target',type=Path)
    p.add_argument('--rows',default='001110,001111,001112,011110,011111,011112,101100,121110,121111,121112')
    p.add_argument('--bench',action='store_true')
    a=p.parse_args(); names=a.rows.split(',')
    if a.bench:
        from bench_boxes import arithmetic_common, region
        code=arithmetic_common+'\n'+maskdef+'\n'+packdef+'\n'+list_mask+'\n'
        for name in names:
            if name!='001110': code+=region('private def boxTable'+name+' :')+'\n'
            code+='#time '+compact_proof(name)+'\n#print axioms boxesArithmetic'+name+'\n'
        code+='end Bench\n'
    else:
        code=replace(a.source.read_text(encoding='utf8'),names)
    a.target.write_bytes(code.encode('utf8')); print('generated',a.target,a.target.stat().st_size)
