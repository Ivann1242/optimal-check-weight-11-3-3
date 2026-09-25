"""Pure [[n,k,3]] stabilizer codes with generator weight <= w, syndrome formulation.

Column j of the m x 2n check matrix gives syndromes a_j = s(Z_j), b_j = s(X_j) in F_2^m.
Pure distance 3  <=>  the 3n vectors a_j, b_j, a_j+b_j are nonzero and pairwise distinct.
Commutation      <=>  sum_j (a_j b_j^T + b_j a_j^T) = 0 (off-diagonal part).
Rank m           <=>  no nonzero y with y.a_j = y.b_j = 0 for all j.
Symmetry breaking: per qubit a_j < b_j < a_j+b_j (integers, row 0 = MSB), and a_0 < a_1 < ... .
Usage: python pure.py n k w [cnf_out]
"""
import sys, itertools, time
from pysat.formula import CNF, IDPool
from pysat.card import CardEnc, EncType
from pysat.solvers import Solver

n, k, w = map(int, sys.argv[1:4])
cnf_out = sys.argv[4] if len(sys.argv) > 4 else None
m = n - k
pool = IDPool(); cnf = CNF()
T = pool.id('T'); cnf.append([T])

def a(i, j): return pool.id(('a', i, j))
def b(i, j): return pool.id(('b', i, j))

def XOR2(x, y):
    z = pool.id(); cnf.extend([[-z, x, y], [-z, -x, -y], [z, -x, y], [z, x, -y]]); return z
def XOR(lits):
    if not lits: return -T
    acc = lits[0]
    for l in lits[1:]: acc = XOR2(acc, l)
    return acc
def AND(x, y):
    z = pool.id(); cnf.extend([[-z, x], [-z, y], [z, -x, -y]]); return z
def OR(lits):
    z = pool.id(); cnf.append([-z] + lits)
    for l in lits: cnf.append([z, -l])
    return z

def lt(x, y):
    """assert x < y as integers, x[0] MSB. x,y lists of literals."""
    eq = T  # prefix equal
    clause = []
    for xi, yi in zip(x, y):
        # strictly less at this position given equal prefix
        d = pool.id()  # d -> eq & ~xi & yi
        cnf.extend([[-d, eq], [-d, -xi], [-d, yi]])
        clause.append(d)
        # new eq = eq & (xi == yi)
        e = pool.id(); x_eq = -XOR2(xi, yi)
        cnf.extend([[-e, eq], [-e, x_eq], [e, -eq, -x_eq]])
        eq = e
    cnf.append(clause)

A = [[a(i, j) for i in range(m)] for j in range(n)]
B = [[b(i, j) for i in range(m)] for j in range(n)]
C = [[XOR2(a(i, j), b(i, j)) for i in range(m)] for j in range(n)]
vecs = [v for j in range(n) for v in (A[j], B[j], C[j])]

for v in vecs: cnf.append(list(v))                       # no weight-1 element of N (case: no wt-1 stabilizer)
for j in range(n):                                        # distinct within a qubit
    for v, u in itertools.combinations((A[j], B[j], C[j]), 2):
        cnf.append([XOR2(x, y) for x, y in zip(v, u)])
def gx(i, q): return a(i, q)   # X-bit of generator i on qubit q
def gz(i, q): return b(i, q)   # Z-bit
for j, l in itertools.combinations(range(n), 2):          # collisions across qubits need E_j F_l in S
    for pj, vj in ((1, A[j]), (2, B[j]), (3, C[j])):      # pj: 1=Z-syndrome->error Z? see below
        for pl, vl in ((1, A[l]), (2, B[l]), (3, C[l])):
            # vj = s(E_j): A = s(Z), B = s(X), C = s(Y)
            ej = {1: (0, 1), 2: (1, 0), 3: (1, 1)}[pj]    # (x,z) bits of error on qubit j
            el = {1: (0, 1), 2: (1, 0), 3: (1, 1)}[pl]
            inS = pool.id()
            c = [pool.id() for _ in range(m)]
            for q in range(n):
                tx = ej[0] if q == j else el[0] if q == l else 0
                tz = ej[1] if q == j else el[1] if q == l else 0
                for tgt, fn in ((tx, gx), (tz, gz)):
                    x = XOR([AND(c[i], fn(i, q)) for i in range(m)])
                    cnf.append([-inS, x if tgt else -x])
            cnf.append([XOR2(x, y) for x, y in zip(vj, vl)] + [inS])
for i in range(m):                                        # weight
    s = [OR([a(i, j), b(i, j)]) for j in range(n)]
    cnf.extend(CardEnc.atmost(s, bound=w, vpool=pool, encoding=EncType.seqcounter).clauses)

for i1, i2 in itertools.combinations(range(m), 2):        # commutation
    terms = [AND(a(i1, j), b(i2, j)) for j in range(n)] + [AND(b(i1, j), a(i2, j)) for j in range(n)]
    cnf.append([-XOR(terms)])

for mask in range(1, 2 ** m):                             # rank m
    idx = [i for i in range(m) if mask >> i & 1]
    cnf.append([XOR([V[i] for i in idx]) for V in (A[j] for j in range(n))] +
               [XOR([V[i] for i in idx]) for V in (B[j] for j in range(n))])

for j in range(n):                                        # LC canonical
    lt(A[j], B[j]); lt(B[j], C[j])
for j in range(n):                                        # g_0 = weight-2 element on {0,1}
    if j < 2: cnf.append([a(0, j), b(0, j)])
    else: cnf.extend([[-a(0, j)], [-b(0, j)]])
def le(x, y):
    t = pool.id(); cnf.append([t])  # x <= y  <=>  not (y < x)
    eq = T; bad = []
    for xi, yi in zip(x, y):
        d = pool.id(); cnf.extend([[-d, eq], [-d, xi], [-d, -yi]]); bad.append(d)
        e = pool.id(); x_eq = -XOR2(xi, yi); cnf.extend([[-e, eq], [-e, x_eq], [e, -eq, -x_eq]]); eq = e
    for d in bad: cnf.append([-d])
for j in range(2, n - 1):
    le(A[j], A[j + 1])

print(f'degen2 n={n} k={k} w={w} vars={pool.top} clauses={len(cnf.clauses)}', flush=True)
if cnf_out:
    cnf.to_file(cnf_out); sys.exit(0)
t0 = time.time()
with Solver(name='cadical195', bootstrap_with=cnf.clauses) as s:
    res = s.solve()
    print('SAT' if res else 'UNSAT', f'{time.time()-t0:.1f}s', flush=True)
    if res:
        mdl = set(l for l in s.get_model() if l > 0)
        for i in range(m):
            print(''.join('IXZY'[(a(i, j) in mdl) + 2 * (b(i, j) in mdl)] for j in range(n)))
