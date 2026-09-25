"""Independent brute-force check of a stabilizer code given as Pauli strings."""
import sys, itertools
gens = [l.strip() for l in open(sys.argv[1]) if l.strip()]
n = len(gens[0]); m = len(gens)
def vec(p): return [c in 'XY' for c in p], [c in 'ZY' for c in p]
def symp(u, v): return (sum(u[0][i] & v[1][i] for i in range(n)) + sum(u[1][i] & v[0][i] for i in range(n))) % 2
def toint(u): return sum((u[0][i] << i) | (u[1][i] << (n + i)) for i in range(n))
V = [vec(g) for g in gens]
assert all(len(g) == n for g in gens)
print('n', n, 'm', m, 'k', n - m, 'max weight', max(sum(c != 'I' for c in g) for g in gens))
assert all(symp(u, v) == 0 for u in V for v in V), 'noncommuting'
# GF(2) rank and span
basis = {}
def reduce(x):
    for b in sorted(basis, reverse=True):
        if x >> b & 1: x ^= basis[b]
    return x
for u in V:
    x = reduce(toint(u)); assert x, 'dependent'
    basis[x.bit_length() - 1] = x
print('independent: rank', len(basis))
dmin = None
for w in range(1, 4):
    for qs in itertools.combinations(range(n), w):
        for ps in itertools.product('XYZ', repeat=w):
            p = ['I'] * n
            for q, c in zip(qs, ps): p[q] = c
            u = vec(p)
            if all(symp(u, v) == 0 for v in V) and reduce(toint(u)) != 0:
                dmin = w; break
        if dmin: break
    if dmin: break
print('distance', dmin if dmin else '>= 4')
