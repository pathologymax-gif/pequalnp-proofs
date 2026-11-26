"""Generate an isolated Lean benchmark from the original PR 23279 source."""
import argparse
from pathlib import Path
import re

source = Path(__file__).with_name('pr23279.lean').read_text(encoding='utf-8').splitlines()


def span(a, b):
    return '\n'.join(source[a-1:b])


def region(opener):
    start = next(i for i,line in enumerate(source) if line.startswith(opener))
    end = next(i for i in range(start + 1,len(source)) if not source[i].strip())
    return '\n'.join(source[start:end])


common = '\n\n'.join(['import Mathlib', 'namespace Bench',
    region('abbrev DisjointRow'), region('def disjointDot'), region('def disjointFormsLinear'),
    region('def disjointResiduesLinear'), region('def disjointResidueLinear'),
    region('def nextDigit'), region('def liftResidueRow'), region('def liftedResidue'),
    region('structure DigitBox'), region('def DigitBox.fits'), region('private def boxedRuleIds'),
    region('structure BoxTable'),region('def BoxTable.digit'),
    region('def BoxTable.valid'),region('private def boxTable001110'),
    'set_option maxRecDepth 32768', 'set_option maxHeartbeats 0', 'set_option Elab.async false'])

arithmetic_common = common + '\n\nopen scoped Classical\n\n' + '\n\n'.join([span(2900,2919),span(5758,5770),span(6013,6034),region('def DigitBox.order'),region('def DigitBox.sign'),span(8360,8462)])


def explicit_row(name):
    """Expand each pure valuation rule by definitional equality, then use omega."""
    from optimize_valuation_boxes import original_arithmetic, table_parts
    equations = dict(re.findall(r'^  \| (49[13579]|501) => (.*)$',span(6013,6034),re.M))
    digits, zeros, boxes = table_parts('boxTable'+name)
    proof = original_arithmetic(name).split('  all_goals simp [boxTable',1)[0]
    branches = []
    for rows, ones, bigger, _, _ in boxes:
        instructions = []
        needed = set()

        def specialize(match):
            index = int(match[1])
            if digits[index]:
                return '(0 : Int)'
            if index in ones:
                return '(1 : Int)'
            needed.add(index)
            return f'(v {index})'

        for i, rule in enumerate(rows):
            if str(rule) not in equations:
                raise ValueError('The fully explicit method requires a table of pure valuation rules.')
            term = re.sub(r'\(v (\d+)\)', specialize, equations[str(rule)].strip())
            instructions += [f'have e{i} := hr {rule} (by decide)',f'change {term} at e{i}']
        for k in sorted(needed):
            if k in bigger:
                instructions.append(f'have h{k} := hb {k} (by decide)')
            elif k in zeros:
                instructions.append(f'have h{k} := hz {k} (by decide)')
        instructions.append('omega')
        branches.append('  · '+'\n    '.join(instructions))
    return proof+'\n'.join(branches)


def benchmark(method, names):
    from optimize_valuation_boxes import maskdef, original_arithmetic, packdef, proof
    from compact_valuation_boxes import compact_proof, list_mask
    code = arithmetic_common+'\n'
    if method in ('lookup','reconstruct'):
        code += maskdef+'\n'+packdef+'\n'
    if method == 'reconstruct':
        code += list_mask+'\n'
    for name in names:
        if name!='001110':
            code += region('private def boxTable'+name+' :')+'\n'
        if method == 'original':
            theorem = original_arithmetic(name)
        elif method == 'explicit':
            theorem = explicit_row(name)
        elif method == 'lookup':
            data,theorem = proof(name)
            code += data+'\n'
        else:
            theorem = compact_proof(name)
        code += '#time '+theorem+'\n#print axioms boxesArithmetic'+name+'\n'
    return code+'end Bench\n'


if __name__=='__main__':
    p=argparse.ArgumentParser(description=__doc__)
    p.add_argument('output',type=Path)
    p.add_argument('--method',choices=('original','explicit','lookup','reconstruct'),default='lookup')
    p.add_argument('--rows',default='001110',help='comma-separated original table labels')
    args=p.parse_args()
    args.output.write_bytes(benchmark(args.method,args.rows.split(',')).encode('utf-8'))
