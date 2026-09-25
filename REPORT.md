# QIQCOP op_458e9e86: no [[11,3,3]] stabilizer code has weight-4 generators

**Answer (negative):** no qubit stabilizer code with parameters [[11,3,d≥3]] has a generating set in which
every generator has weight at most 4. Together with the weight-5 construction of Wei et al., this gives
W_opt(11,3,3) = 5.

**By-product (positive):** an explicit [[12,3,3]] code whose generators all have weight at most 4. This
gives W_opt(12,3,3) = 4, which Wei et al.'s Table II lists as "4–5". It also settles n = 13 and 14,
because W_opt is nonincreasing in n. So the least length of an [[n,3,3]] code with weight-4 generators
is exactly **12**.

```
IIIIIIZZIIZZ
IIIIIIIIZZXX
ZZIIIIIIXXII
IIIIZZXXIIII
IIIZIXIYIIIX
ZIZIXXIIIIII
IZXXIZIIIIII
IXIYIIIIIYIZ
XIIIYIZIZIII
```

A brute-force checker, written independently of the SAT encoding (`verify_code.py`), confirms:
- 9 generators;
- they pairwise commute and are independent over GF(2);
- the maximum weight is 4;
- no Pauli of weight 1 or 2 lies in N(S)\S;
- the distance is exactly 3.

## Proof of the negative result (computer-assisted, DRAT-certified)

Notation:
- m = n − k.
- The i-th generator has X-bits x_{ij} and Z-bits z_{ij}.
- For qubit j, write a_j = s(Z_j) = (x_{ij})_i and b_j = s(X_j) = (z_{ij})_i, both in F₂^m. The syndrome of
  Y_j is a_j + b_j.

Commutation is Σ_j (a_j b_jᵀ + b_j a_jᵀ) = 0 (off-diagonal). Independence means the 2n columns span F₂^m.

Distance ≥ 3 means: every Pauli of weight ≤ 2 whose syndrome is zero lies in S.

For every 4 ≤ n ≤ 11, we show that no [[n,3,≥3]] code with generator weight ≤ 4 exists. We use induction
on n; for n = 3, m = 0 and the distance is 1. S is split into exactly one of three cases.

**(A) S contains a weight-1 element.**
- After a qubit permutation and a local Clifford, the element is Z₀.
- Multiply the other generators by Z₀ to clear their qubit-0 component. This never increases the weight.
  Commutation with Z₀ forbids X or Y on qubit 0.
- The code is then |0⟩ ⊗ C′. Here C′ is an [[n−1,3]] code whose m−1 generators have weight ≤ 4.
- A logical operator of C′ with weight ≤ 2 lifts to one of C, so d(C′) ≥ 3.
- This contradicts the induction hypothesis for n − 1.

**(B) S has weight-2 elements but no weight-1 element.**
- Let W be the span of the weight-2 elements of S, and r = dim W.
- By the exchange lemma, a basis of W made of weight-2 elements can be extended by original generators
  to a generating set of S. Every generator still has weight ≤ 4, and the W-basis comes first.
- With no weight-1 element, all 3n single-qubit syndromes are nonzero, and they are distinct within each
  qubit.
- Two syndromes from different qubits may coincide only if the weight-2 product lies in S, hence in W.
  This is encoded with coefficient variables over the r W-generators.
- For r = 1 and r = 2, the supports of the W-generators are fixed WLOG to one of: {0,1}; {0,1},{0,1};
  {0,1},{1,2}; {0,1},{2,3}. Every element of W is supported inside the first t ≤ 4 qubits. So pairs involving
  a qubit ≥ t must have distinct syndromes, and those qubits are sorted strictly.

**(C) Pure case: S has no element of weight ≤ 2.**
- d ≥ 3 is then equivalent to the 3n syndromes being nonzero and pairwise distinct.
- Equivalently, the n planes span{a_j, b_j} ≤ F₂^m meet pairwise trivially.

**Symmetry breaking** (all sound):
- For each qubit, a local Clifford permutes {a_j, b_j, a_j+b_j} arbitrarily (GL(2,2) ≅ S₃), so we impose
  a_j < b_j < a_j + b_j as integers.
- Qubits outside the fixed supports are sorted by a_j. The order is strict whenever those syndromes are
  forced to be distinct.

**SAT instances.** Every instance is UNSAT. CaDiCaL 2.x produced a DRAT proof for each, and drat-trim
checked it: `s VERIFIED`.

| n | pure (C) | degenerate (B) |
|---|---|---|
| 4–9 | `pure_n` | `degen_n` (all r at once) |
| 10 | `pure_10` | r=1,2: `ds_10_{one,same,chain,disj}`; r=3..7: `dr_10_r` |
| 11 | `pure_11` | r=1,2: `ds_11_{one,same,chain,disj}`; r=3..8: `dr_11_r` |

**Validation of the encoding.** The same case-split pipeline reproduces Wei et al.'s published values
W_opt(n,k,3), listed in the cross-check table below. It also finds [[5,1,3]], [[8,3,3]], the Shor code (in
the degenerate encoder), and the new [[12,3,3]] code. Each was re-checked by the independent brute-force
checker.

**Trust base:**
- the reductions (A)–(C) and the symmetry-breaking arguments above, which are short and human-checkable;
- the Python CNF generators (`pure.py`, `degen.py`, `degenr.py`, `degens.py`);
- drat-trim.

The solvers themselves are not trusted.

The search, proof and write-up were done by Claude (Anthropic), with Yifan Jing directing, in Claude Code
on 2026-09-24.
