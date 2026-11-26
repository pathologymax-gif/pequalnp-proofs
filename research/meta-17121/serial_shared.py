"""Check two possibly dependent shared gates by a common cofactor.

Run python serial_shared.py to replay. Add --generate to rebuild the bundle
using SciPy and the adjacent kw_first_shared.py generator.
"""
import argparse
from collections import Counter
import gzip
from itertools import combinations
import json
from pathlib import Path
from time import monotonic

from verify_kw_first_shared import check_tree


def main():
    if not __debug__:
        raise RuntimeError('Run Python with assertions enabled.')
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--generate',action='store_true')
    args=parser.parse_args()
    here=Path(__file__).resolve().parent
    source=json.loads((here/'seed_tables.json').read_text())
    path=here/'serial_shared.json.gz'
    if args.generate:
        from kw_first_shared import generate
        evidence=[]
    else:
        evidence=json.loads(gzip.decompress(path.read_bytes()))
        assert len(source)==len(evidence)==4
    for index,row in enumerate(source):
        saved={} if args.generate else evidence[index]
        expected=set()
        counts=Counter()
        active=[j for j,w in enumerate(row) if w]
        assert len(active)==10
        for a,b in combinations(active,2):
            key=f'{a}-{b}'
            expected.add(key)
            table=[w & (16383|row[a]|row[b]) for w in row]
            if args.generate:
                for limit in (16,15,14):
                    result=generate(table,monotonic()+30,limit)
                    if set(result)=={'tree'}:
                        saved[key]=[limit,result['tree']]
                        break
            lower,tree=saved[key]
            assert lower in (14,15,16)
            counts[lower]+=1
            counts['leaves']+=check_tree(table,tree,lower)
        assert set(saved)==expected and len(saved)==45
        if args.generate:
            evidence.append(saved)
        print(index,dict(counts),flush=True)
    if args.generate:
        path.write_bytes(gzip.compress(json.dumps(evidence,separators=(',',':')).encode(),mtime=0))


if __name__=='__main__':
    main()
