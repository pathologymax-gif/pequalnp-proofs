"""Finite clique obstructions for the AND budget of an individual clean term."""

from functools import cache
from itertools import combinations


def find_clique(neighbors, size):
    def visit(options, left):
        if left == 0:
            return ()
        while options.bit_count() >= left:
            v = options & -options
            options ^= v
            i = v.bit_length()-1
            rest = visit(options & neighbors[i],left-1)
            if rest is not None:
                return (i,)+rest
        return None
    return visit((1 << len(neighbors)) - 1, size)


@cache
def positive_obstructions(words):
    positives = list(range(14))
    masks = [sum(1 << i for i, w in enumerate(words) if w >> j & 1) for j in range(32)]
    negatives = sorted(set(masks[14:])-{0})
    assert all(masks[p].bit_count()==2 for p in positives)
    live = [i for i,w in enumerate(words) if w]
    for q in negatives:
        assert not any(masks[p] & ~q == 0 for p in positives)
        assert all(any(masks[p] & ~(q | (1<<i)) == 0 for p in positives)
                   for i in live if not (q >> i & 1))
    graph = []
    for p in positives:
        graph.append(tuple(sum(1<<j for j,r in enumerate(negatives)
                            if q!=r and masks[p] & ~(q|r)==0) for q in negatives))
    result = {}
    for extra in range(1,5):
        # If <=extra-1 core ANDs occur then the terminal has <=extra ANDs
        # in its cone and cannot separate a clique with 2**extra+1 vertices.
        need = (1<<extra)+1
        if need>len(negatives):
            continue
        minimal = []
        for size in range(1,15):
            for es in combinations(positives,size):
                bitset = sum(1<<i for i in es)
                if any(m & ~bitset == 0 for m in minimal):
                    continue
                neighbors = [0]*len(negatives)
                for p in es:
                    for j, nbr in enumerate(graph[p]):
                        neighbors[j] |= nbr
                clique = find_clique(neighbors,need)
                if clique is not None:
                    assert len(set(clique)) == need
                    assert all(any(masks[p] & ~(negatives[i]|negatives[j])==0 for p in es)
                               for i,j in combinations(clique,2))
                    minimal.append(bitset)
        result[extra] = minimal
    return result
