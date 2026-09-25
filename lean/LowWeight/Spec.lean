import Mathlib

/-!
# Boolean specifications handed to `bv_decide`

A family of `m` generators on `n` qubits is stored as bit matrices `x z : Fin m → Fin n → Bool`
(`x i j` / `z i j` = X-bit / Z-bit of generator `i` on qubit `j`). The syndrome of the single-qubit error
of type `t` on qubit `j` (t = 0: Z, t = 1: X, t = 2: Y) is the column `syn x z j t : Fin m → Bool`.
-/

namespace LowWeight

variable {m n : ℕ}

/-- Syndrome bit of the error of type `t` on qubit `j` against generator `i`. -/
def syn (x z : Fin m → Fin n → Bool) (j : Fin n) (t : Fin 3) (i : Fin m) : Bool :=
  if t = 0 then x i j else if t = 1 then z i j else xor (x i j) (z i j)

/-- Strict lexicographic order on columns, index `0` most significant. -/
def colLt (u v : Fin m → Bool) : Prop :=
  ∃ p : Fin m, (∀ q : Fin m, q < p → u q = v q) ∧ u p = false ∧ v p = true

/-- Non-strict version. -/
def colLe (u v : Fin m → Bool) : Prop := u = v ∨ colLt u v

/-- Number of qubits on which generator `i` acts, as a 4-bit counter (`n ≤ 15`). -/
def rowWt (x z : Fin m → Fin n → Bool) (i : Fin m) : BitVec 4 :=
  ∑ j, if (x i j || z i j) then 1 else 0

/-- Symplectic product of generators `i₁ i₂`, as a 1-bit sum. -/
def rowSymp (x z : Fin m → Fin n → Bool) (i₁ i₂ : Fin m) : BitVec 1 :=
  ∑ j, if ((x i₁ j && z i₂ j) ^^ (z i₁ j && x i₂ j)) then 1 else 0

/-- Conditions shared by all cases: weights `≤ w`, commutation, nonzero single-qubit syndromes,
distinct syndromes within each qubit, and the local-Clifford normal form `a < b < a+b`. -/
def CommonSpec (w : ℕ) (x z : Fin m → Fin n → Bool) : Prop :=
  (∀ i, rowWt x z i ≤ BitVec.ofNat 4 w) ∧
  (∀ i₁ i₂, rowSymp x z i₁ i₂ = 0) ∧
  (∀ j t, ∃ i, syn x z j t i = true) ∧
  (∀ j, colLt (syn x z j 0) (syn x z j 1) ∧ colLt (syn x z j 1) (syn x z j 2))

/-- Pure case: all `3n` single-qubit syndromes pairwise distinct; qubits strictly sorted. -/
def PureSpec (w : ℕ) (x z : Fin m → Fin n → Bool) : Prop :=
  CommonSpec w x z ∧
  (∀ j l : Fin n, j < l → ∀ t s : Fin 3, ∃ i, syn x z j t i ≠ syn x z l s i) ∧
  (∀ j l : Fin n, j.val + 1 = l.val → colLt (syn x z j 0) (syn x z l 0))

/-- X-bit and Z-bit of the single-qubit error of type `t` (0: Z, 1: X, 2: Y). -/
def ex (t : Fin 3) : Bool := t ≠ 0
def ez (t : Fin 3) : Bool := t ≠ 1

/-- Generator `i` is supported exactly on the qubit set `S`. -/
def SuppIs (x z : Fin m → Fin n → Bool) (i : Fin m) (S : Finset (Fin n)) : Prop :=
  ∀ j, (x i j || z i j) = decide (j ∈ S)

/-- `∑ᵢ cᵢ gᵢ` equals the two-qubit error `E_j^t F_l^s` (`j ≠ l`), as bit equations. -/
def SpanEq (x z : Fin m → Fin n → Bool) (c : Fin m → Bool) (j l : Fin n) (t s : Fin 3) : Prop :=
  ∀ q : Fin n,
    (∑ i, if (c i && x i q) then (1 : BitVec 1) else 0) =
      (if ((decide (q = j) && ex t) || (decide (q = l) && ex s)) then 1 else 0) ∧
    (∑ i, if (c i && z i q) then (1 : BitVec 1) else 0) =
      (if ((decide (q = j) && ez t) || (decide (q = l) && ez s)) then 1 else 0)

/-- Degenerate case with explicit supports of the `r` weight-two generators spanning `W`
(used for `r = 1, 2`). All elements of `W` live on qubits `< tt`: pairs meeting qubits `≥ tt` have
distinct syndromes; collisions inside `[0, tt)` are explained by an element `∑ c i • g i`,
`c` supported on the first `r` generators; qubits `≥ tt` are strictly sorted. -/
def DegenLayoutSpec (w r tt : ℕ) (S : Fin m → Finset (Fin n)) (x z : Fin m → Fin n → Bool)
    (c : Fin n → Fin n → Fin 3 → Fin 3 → Fin m → Bool) : Prop :=
  CommonSpec w x z ∧
  (∀ i : Fin m, i.val < r → SuppIs x z i (S i)) ∧
  (∀ j l : Fin n, j < l → tt ≤ l.val → ∀ t s : Fin 3, ∃ i, syn x z j t i ≠ syn x z l s i) ∧
  (∀ j l : Fin n, j < l → l.val < tt → ∀ t s : Fin 3,
    (∃ i, syn x z j t i ≠ syn x z l s i) ∨
      ((∀ i : Fin m, r ≤ i.val → c j l t s i = false) ∧ SpanEq x z (c j l t s) j l t s)) ∧
  (∀ j l : Fin n, tt ≤ j.val → j.val + 1 = l.val → colLt (syn x z j 0) (syn x z l 0))

/-- Degenerate case, general `r`: generator 0 is supported exactly on qubits `{0, 1}`, generators
`1, …, r-1` have weight `≤ 2`, every syndrome collision between two qubits is explained by an
element of the span of the first `r` generators, and qubits `≥ 2` are sorted (non-strictly). -/
def DegenGenSpec (w r : ℕ) (x z : Fin m → Fin n → Bool)
    (c : Fin n → Fin n → Fin 3 → Fin 3 → Fin m → Bool) : Prop :=
  CommonSpec w x z ∧
  (∀ i : Fin m, i.val = 0 → ∀ j : Fin n, (x i j || z i j) = decide (j.val < 2)) ∧
  (∀ i : Fin m, i.val < r → rowWt x z i ≤ 2) ∧
  (∀ j l : Fin n, j < l → ∀ t s : Fin 3,
    (∃ i, syn x z j t i ≠ syn x z l s i) ∨
      ((∀ i : Fin m, r ≤ i.val → c j l t s i = false) ∧ SpanEq x z (c j l t s) j l t s)) ∧
  (∀ j l : Fin n, 2 ≤ j.val → j.val + 1 = l.val → colLe (syn x z j 0) (syn x z l 0))

end LowWeight
