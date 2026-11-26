"""Find all minimal inputs absent from the order-three plane's negative sample family."""
from collections import Counter
from itertools import combinations
import json
from pathlib import Path

POINTS = range(13)
ALL_POINTS = (1 << 13) - 1
D = (0, 1, 3, 9)
LINES = tuple(sum(1 << ((a + i) % 13) for a in D) for i in POINTS)


def facets():
    for q in combinations(POINTS, 4):
        point_set = sum(1 << p for p in q)
        if all((point_set & l).bit_count() <= 2 for l in LINES):
            line_set = sum(1 << j for j, l in enumerate(LINES) if not point_set & l)
            assert line_set.bit_count() == 3
            yield point_set | (line_set << 13)


def subsets(s):
    j = s
    while True:
        yield j
        if j == 0:
            return
        j = (j - 1) & s


def minimal_nonfaces():
    neg = list(facets())
    faces = {s for n in neg for s in subsets(n)}
    # Any minimal absent set is obtained by extending an actual face by
    # one vertex. All immediate subsets must occur in a negative sample.
    boundary = set()
    for s in faces:
        for k in range(26):
            t = s | (1 << k)
            if t not in faces and all((t ^ (1 << j)) in faces for j in range(26) if t >> j & 1):
                boundary.add(t)
    incidence = {1 << p | 1 << (13 + j) for j, l in enumerate(LINES) for p in POINTS if l >> p & 1}
    assert {s for s in boundary if s.bit_count() <= 2} == incidence
    return neg, faces, incidence, boundary


if __name__ == '__main__':
    neg, faces, edges, absent = minimal_nonfaces()
    counts = Counter(((s & ALL_POINTS).bit_count(), (s >> 13).bit_count()) for s in absent)
    print('negative samples', len(neg), 'faces', len(faces), 'incidences', len(edges))
    for key, size in sorted(counts.items(), key=lambda pair: (sum(pair[0]), pair[0])):
        print(key, size)
    result = {'negative_samples': len(neg), 'faces': len(faces), 'incidences': len(edges),
              'minimal_nonfaces': [dict(points=p, lines=l, count=n) for (p, l), n in sorted(counts.items())]}
    Path(__file__).with_name('quadrangle_counts.json').write_text(json.dumps(result, indent=2) + '\n')
