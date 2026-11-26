"""Synthesize AND/OR/NOT formula witnesses on the 16 one-left/one-right inputs."""
import json
from pathlib import Path


TARGETS = {
    19039: (4732, 9), 19040: (4733, 9), 19041: (4990, 9), 19042: (5755, 9),
    19043: (5805, 9), 19044: (5821, 9), 19045: (5822, 9), 19046: (13758, 9),
    19047: (4414, 8), 19048: (4459, 8), 19049: (4478, 8), 19050: (4699, 8),
    19051: (4700, 8), 19052: (4701, 8), 19053: (4702, 8), 19054: (4830, 8),
    19055: (4958, 8), 19056: (4972, 8), 19057: (4973, 8),
}
ALL = (1 << 16) - 1
RAW = [15 << (4 * i) for i in range(4)] + [0x1111 << j for j in range(4)]


def formulas(max_size):
    descriptor = {value: ('raw', i, i) for i, value in enumerate(RAW)}
    levels = [list(RAW)]
    for cost in range(1, max_size + 1):
        level = []
        for a in levels[cost - 1]:
            value = ALL ^ a
            if value not in descriptor:
                descriptor[value] = ('not', a, a)
                level.append(value)
        for i in range((cost - 1) // 2 + 1):
            j = cost - i - 1
            low, high = levels[i], levels[j]
            for index, a in enumerate(low):
                for b in high[index+1:] if i == j else high:
                    value = a & b
                    if value not in descriptor:
                        descriptor[value] = ('and', a, b)
                        level.append(value)
                    value = a | b
                    if value not in descriptor:
                        descriptor[value] = ('or', a, b)
                        level.append(value)
        print(f'cost {cost}: {len(level)} new masks, {len(descriptor)} total', flush=True)
        levels.append(level)
    return descriptor


def gates_for(word, descriptor):
    wires = dict(zip(RAW, range(8)))
    gates = []

    def visit(value):
        if value in wires:
            return wires[value]
        op, left, right = descriptor[value]
        a = visit(left)
        b = visit(right)
        wire = 8 + len(gates)
        gates.append([op, a, b])
        wires[value] = wire
        return wire
    output = visit(word)
    return gates, output


def evaluate_on_pairs(gates, output):
    result = 0
    for u in range(4):
        for v in range(4):
            w = [i == u or i == 4 + v for i in range(8)]
            for op, a, b in gates:
                w.append({'and': w[a] and w[b], 'or': w[a] or w[b], 'not': not w[a]}[op])
            result |= int(w[output]) << (4*u+v)
    return result


if __name__ == '__main__':
    terms = formulas(max(limit for _, limit in TARGETS.values()))
    witnesses = {}
    for step, (word, limit) in TARGETS.items():
        if word not in terms:
            continue
        gates, out = gates_for(word, terms)
        assert evaluate_on_pairs(gates, out) == word
        if len(gates) <= limit:
            witnesses[str(step)] = dict(mask=word, bound=limit, gates=gates, output=out)
    (Path(__file__).parent/'formula_witnesses.json').write_text(json.dumps(witnesses, indent=2))
    print('Eligible witnesses:', {k: len(v['gates']) for k, v in witnesses.items()})
