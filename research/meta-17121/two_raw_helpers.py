"""Exact KW lower bounds for two shared gates, each an OR of two raw variables."""
import argparse
from collections import Counter
from functools import cache
import gzip
from itertools import combinations
import json
from pathlib import Path
from time import monotonic

from kw_first_shared import generate, replay


ROOT = Path(__file__).resolve().parent
TARGET = 16383


def make_screen(inputs):
    edges = [tuple(i for i, w in enumerate(inputs) if w >> b & 1) for b in range(14)]

    @cache
    def cover(edge_mask):
        if not edge_mask:
            return 0
        a, b = edges[(edge_mask & -edge_mask).bit_length() - 1]
        return 1 + min(cover(edge_mask & ~inputs[v]) for v in (a, b))

    def lower(helpers):
        rowsets = [0] * len(inputs)
        colsets = [0] * len(inputs)
        for j, (a, b) in enumerate(edges):
            unavailable = 0xffffffff ^ TARGET
            for h in helpers:
                if h >> j & 1:
                    unavailable &= h
            for v, other in ((a, b), (b, a)):
                cols = inputs[other] & unavailable
                if cols:
                    rowsets[v] |= 1 << j
                    colsets[v] |= cols
        conflict = sum(1 << j for j, (a, b) in enumerate(edges)
                       if rowsets[a] & rowsets[b] and colsets[a] & colsets[b])
        return 2 * len(helpers) + sum(bool(s) for s in rowsets) + cover(conflict)

    return lower


def dual_check(observation, limit, deadline):
    result = generate(observation, deadline, limit)
    status, _ = replay(observation, result, limit)
    return result if status == 'excluded' else None


def cofactor(inputs, helpers, fixed):
    # Fixing a helper to one preserves every positive sample. Retain all
    # negatives on which the fixed helper already had value one.
    negative = 0xffffffff ^ TARGET
    live_helpers = []
    for h, bit in zip(helpers, fixed):
        if bit == 1:
            negative &= h
        elif bit is None:
            live_helpers.append(h)
        else:
            raise ValueError('Unknown helper restriction')
    return [w & (TARGET | negative) for w in inputs + live_helpers] if negative else None


def run(row, mode):
    inputs = json.loads((ROOT / 'seed_tables.json').read_text())[row]
    inputs = [v for v in inputs if v]
    pairs = list(combinations(range(len(inputs)), 2))
    lower = make_screen(inputs)
    summary = Counter()
    path = ROOT / f'kw_two_raw_{row}.json.gz'
    certificates = json.loads(gzip.decompress(path.read_bytes())) if path.exists() else {}
    remainder = []
    needed = set()
    for (a, b), (c, d) in combinations(pairs, 2):
        name = f'{a}-{b}_{c}-{d}'
        hs = [inputs[a] | inputs[b], inputs[c] | inputs[d]]
        if lower(hs) > 17:
            summary['forced rectangles'] += 1
            continue
        if mode == 'screen':
            summary['remaining'] += 1
            continue
        needed.add(name)
        proofs = certificates.get(name)
        if proofs is None and mode == 'replay':
            remainder.append(name)
            continue
        if proofs is None:
            # Fixing two shared inputs removes at least four variable occurrences
            # from the exterior formula. Fixing just one removes at least two.
            priority = [(1, 1), (1, None), (None, 1), (None, None)]
            for fixed in priority:
                table = cofactor(inputs, hs, fixed)
                if table is None:
                    continue
                limit = 17 - 2 * sum(b is not None for b in fixed)
                result = dual_check(table, limit, monotonic() + (75 if fixed == (None, None) else 8))
                if result:
                    proofs = [fixed, result]
                    certificates[name] = proofs
                    break
        if not proofs:
            remainder.append(name)
            continue
        fixed, result = proofs
        assert len(fixed) == 2 and all(bit in (1, None) for bit in fixed)
        table = cofactor(inputs, hs, fixed)
        limit = 17 - 2 * sum(b is not None for b in fixed)
        status, _ = replay(table, result, limit)
        assert status == 'excluded'
        summary[str(fixed)] += 1
    if mode == 'generate':
        path.write_bytes(gzip.compress(json.dumps(certificates, separators=(',', ':')).encode(), mtime=0))
    if mode == 'replay' and (remainder or set(certificates) != needed):
        raise ValueError(f'Incomplete certificate set for row {row}: {remainder}')
    print(row, dict(summary), 'unresolved', len(remainder), remainder[:12], flush=True)
    return remainder


if __name__ == '__main__':
    if not __debug__:
        raise RuntimeError('Replay requires an interpreter with assertions enabled')
    parser = argparse.ArgumentParser()
    parser.add_argument('row', type=int, choices=range(4))
    parser.add_argument('mode', choices=['screen', 'generate', 'replay'])
    args = parser.parse_args()
    run(args.row, args.mode)
