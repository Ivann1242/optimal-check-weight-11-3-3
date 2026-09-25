import Mathlib

/-!
# Weight-constrained stabilizer codes

An `n`-qubit Pauli operator modulo phase is a vector `v : Fin n → F × F` over `F = ZMod 2`;
`(v j).1` is the X-bit and `(v j).2` the Z-bit on qubit `j`. This is the vector `(a, b) ∈ F₂^{2n}`
of the QIQCOP statement (op_458e9e86), written qubit-by-qubit.
-/

namespace LowWeight

abbrev F := ZMod 2

/-- `n`-qubit Pauli operators modulo phase. -/
abbrev Pauli (n : ℕ) := Fin n → F × F

/-- Weight: number of qubits on which the operator acts nontrivially. -/
def wt {n : ℕ} (v : Pauli n) : ℕ := (Finset.univ.filter fun j => v j ≠ 0).card

/-- The symplectic form `⟨(a,b),(a',b')⟩ = a·b' + b·a'`. Two Paulis commute iff it vanishes. -/
def symp {n : ℕ} (u v : Pauli n) : F := ∑ j, ((u j).1 * (v j).2 + (u j).2 * (v j).1)

/-- The conditions of Eq. (458e-conditions), for `n` qubits, `m` generators and weight bound `w`:
the generators are linearly independent, have weight at most `w`, pairwise commute, and every
operator of weight 1 or 2 commuting with all of them lies in their span (distance `≥ 3`). -/
def IsCode (n m w : ℕ) (g : Fin m → Pauli n) : Prop :=
  LinearIndependent F g ∧ (∀ i, wt (g i) ≤ w) ∧ (∀ i j, symp (g i) (g j) = 0) ∧
    ∀ v : Pauli n, 1 ≤ wt v → wt v ≤ 2 → (∀ i, symp v (g i) = 0) →
      v ∈ Submodule.span F (Set.range g)

end LowWeight
