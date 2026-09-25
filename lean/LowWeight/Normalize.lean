import LowWeight.BitDefs

/-! Normal forms: order facts for `colLt`, the local-Clifford canonical form, and sorting of the
qubits from a given index on. -/

namespace LowWeight

variable {m n : ℕ}

/-! ### Order facts -/

theorem colLt_iff_toLex_lt (u v : Fin m → Bool) : colLt u v ↔ toLex u < toLex v := by
  show _ ↔ ∃ i, (∀ j, j < i → u j = v j) ∧ u i < v i
  simp only [colLt, Bool.lt_iff]

theorem colLe_iff_toLex_le (u v : Fin m → Bool) : colLe u v ↔ toLex u ≤ toLex v := by
  rw [le_iff_eq_or_lt, colLe, colLt_iff_toLex_lt, toLex_inj]
  exact Iff.rfl

theorem colLt_irrefl (u : Fin m → Bool) : ¬ colLt u u := by
  rw [colLt_iff_toLex_lt]; exact lt_irrefl _

theorem colLt_trans {u v w : Fin m → Bool} (h1 : colLt u v) (h2 : colLt v w) : colLt u w := by
  rw [colLt_iff_toLex_lt] at *; exact h1.trans h2

theorem colLt_asymm {u v : Fin m → Bool} (h1 : colLt u v) : ¬ colLt v u := fun h2 =>
  colLt_irrefl u (colLt_trans h1 h2)

theorem colLt_trichotomy {u v : Fin m → Bool} (h : u ≠ v) : colLt u v ∨ colLt v u := by
  simp only [colLt_iff_toLex_lt]
  exact lt_or_gt_of_ne fun e => h (toLex_inj.mp e)

theorem colLt_of_colLe_of_ne {u v : Fin m → Bool} (h : colLe u v) (hne : u ≠ v) : colLt u v :=
  h.resolve_left hne

/-! ### Permutations -/

theorem synP_permP (τ : Equiv.Perm (Fin n)) (g : Fin m → Pauli n) (j : Fin n) (t : Fin 3) :
    synP (fun i => permP τ (g i)) j t = synP g (τ j) t := rfl

/-! ### Local-Clifford canonical form -/

/-- X-bit and Z-bit of a single-qubit Pauli. -/
def bx (p : F × F) : Bool := decide (p.1 = 1)
def bz (p : F × F) : Bool := decide (p.2 = 1)

theorem synP_zero (g : Fin m → Pauli n) (j : Fin n) : synP g j 0 = fun i => bx (g i j) := by
  funext i; simp [synP, syn, toX, bx]

theorem synP_one (g : Fin m → Pauli n) (j : Fin n) : synP g j 1 = fun i => bz (g i j) := by
  funext i; simp [synP, syn, toZ, bz]

theorem synP_two (g : Fin m → Pauli n) (j : Fin n) :
    synP g j 2 = fun i => xor (bx (g i j)) (bz (g i j)) := by
  funext i; simp [synP, syn, toX, toZ, bx, bz]

/-- The linear map with matrix `[[a, b], [c, d]]`. -/
def lm (a b c d : F) : (F × F) →ₗ[F] (F × F) where
  toFun p := (a * p.1 + b * p.2, c * p.1 + d * p.2)
  map_add' p q := by ext <;> simp <;> ring
  map_smul' r p := by ext <;> simp <;> ring

def mkE (f g : (F × F) →ₗ[F] (F × F)) (h1 : ∀ p, f (g p) = p) (h2 : ∀ p, g (f p) = p) :
    (F × F) ≃ₗ[F] (F × F) :=
  LinearEquiv.ofLinearMap f g (LinearMap.ext h1) (LinearMap.ext h2)

/-- `(x, z) ↦ (x, z)` -/
def E1 : (F × F) ≃ₗ[F] (F × F) := mkE (lm 1 0 0 1) (lm 1 0 0 1) (by decide) (by decide)
/-- `(x, z) ↦ (z, x)` -/
def E2 : (F × F) ≃ₗ[F] (F × F) := mkE (lm 0 1 1 0) (lm 0 1 1 0) (by decide) (by decide)
/-- `(x, z) ↦ (x, x + z)` -/
def E3 : (F × F) ≃ₗ[F] (F × F) := mkE (lm 1 0 1 1) (lm 1 0 1 1) (by decide) (by decide)
/-- `(x, z) ↦ (x + z, x)` -/
def E4 : (F × F) ≃ₗ[F] (F × F) := mkE (lm 1 1 1 0) (lm 0 1 1 1) (by decide) (by decide)
/-- `(x, z) ↦ (z, x + z)` -/
def E5 : (F × F) ≃ₗ[F] (F × F) := mkE (lm 0 1 1 1) (lm 1 1 1 0) (by decide) (by decide)
/-- `(x, z) ↦ (x + z, z)` -/
def E6 : (F × F) ≃ₗ[F] (F × F) := mkE (lm 1 1 0 1) (lm 1 1 0 1) (by decide) (by decide)

/-- Single-qubit version of the canonical form. -/
theorem exists_local1 (v : Fin m → F × F)
    (h01 : (fun i => bx (v i)) ≠ (fun i => bz (v i)))
    (h02 : (fun i => bx (v i)) ≠ fun i => xor (bx (v i)) (bz (v i)))
    (h12 : (fun i => bz (v i)) ≠ fun i => xor (bx (v i)) (bz (v i))) :
    ∃ M : (F × F) ≃ₗ[F] (F × F),
      colLt (fun i => bx (M (v i))) (fun i => bz (M (v i))) ∧
      colLt (fun i => bz (M (v i))) (fun i => xor (bx (M (v i))) (bz (M (v i)))) := by
  rcases colLt_trichotomy h01 with hab | hba <;>
  rcases colLt_trichotomy h02 with hac | hca <;>
  rcases colLt_trichotomy h12 with hbc | hcb
  · exact ⟨E1,
      by convert hab using 1 <;> funext i <;> generalize v i = p <;> revert p <;> decide,
      by convert hbc using 1 <;> funext i <;> generalize v i = p <;> revert p <;> decide⟩
  · exact ⟨E3,
      by convert hac using 1 <;> funext i <;> generalize v i = p <;> revert p <;> decide,
      by convert hcb using 1 <;> funext i <;> generalize v i = p <;> revert p <;> decide⟩
  · exact absurd (colLt_trans (colLt_trans hbc hca) hab) (colLt_irrefl _)
  · exact ⟨E4,
      by convert hca using 1 <;> funext i <;> generalize v i = p <;> revert p <;> decide,
      by convert hab using 1 <;> funext i <;> generalize v i = p <;> revert p <;> decide⟩
  · exact ⟨E2,
      by convert hba using 1 <;> funext i <;> generalize v i = p <;> revert p <;> decide,
      by convert hac using 1 <;> funext i <;> generalize v i = p <;> revert p <;> decide⟩
  · exact absurd (colLt_trans (colLt_trans hac hcb) hba) (colLt_irrefl _)
  · exact ⟨E5,
      by convert hbc using 1 <;> funext i <;> generalize v i = p <;> revert p <;> decide,
      by convert hca using 1 <;> funext i <;> generalize v i = p <;> revert p <;> decide⟩
  · exact ⟨E6,
      by convert hcb using 1 <;> funext i <;> generalize v i = p <;> revert p <;> decide,
      by convert hba using 1 <;> funext i <;> generalize v i = p <;> revert p <;> decide⟩

theorem exists_localCanon (g : Fin m → Pauli n)
    (hd : ∀ j, synP g j 0 ≠ synP g j 1 ∧ synP g j 0 ≠ synP g j 2 ∧ synP g j 1 ≠ synP g j 2) :
    ∃ M : Fin n → (F × F) ≃ₗ[F] (F × F), ∀ j,
      colLt (synP (fun i => localP M (g i)) j 0) (synP (fun i => localP M (g i)) j 1) ∧
      colLt (synP (fun i => localP M (g i)) j 1) (synP (fun i => localP M (g i)) j 2) := by
  have h : ∀ j, ∃ M : (F × F) ≃ₗ[F] (F × F),
      colLt (fun i => bx (M (g i j))) (fun i => bz (M (g i j))) ∧
      colLt (fun i => bz (M (g i j))) (fun i => xor (bx (M (g i j))) (bz (M (g i j)))) := by
    intro j
    obtain ⟨h01, h02, h12⟩ := hd j
    simp only [synP_zero, synP_one, synP_two] at h01 h02 h12
    exact exists_local1 (fun i => g i j) h01 h02 h12
  choose M hM using h
  refine ⟨M, fun j => ?_⟩
  rw [synP_zero, synP_one, synP_two]
  exact hM j

/-! ### Sorting the tail -/

/-- Extend a permutation of `Fin (n - t0)` to `Fin n`, fixing the first `t0` qubits. -/
def extF (t0 : ℕ) (σ : Equiv.Perm (Fin (n - t0))) (j : Fin n) : Fin n :=
  if h : j.val < t0 then j
  else ⟨t0 + (σ ⟨j.val - t0, by have := j.isLt; omega⟩).val,
    by have := (σ ⟨j.val - t0, by have := j.isLt; omega⟩).isLt; omega⟩

theorem extF_lt (t0 : ℕ) (σ : Equiv.Perm (Fin (n - t0))) (j : Fin n) (h : j.val < t0) :
    extF t0 σ j = j := by simp [extF, h]

theorem extF_ge (t0 : ℕ) (σ : Equiv.Perm (Fin (n - t0))) (j : Fin n) (h : t0 ≤ j.val) :
    (extF t0 σ j).val = t0 + (σ ⟨j.val - t0, by have := j.isLt; omega⟩).val := by
  unfold extF; simp [show ¬ j.val < t0 by omega]

theorem extF_extF (t0 : ℕ) (σ : Equiv.Perm (Fin (n - t0))) (j : Fin n) :
    extF t0 σ (extF t0 σ⁻¹ j) = j := by
  by_cases h : j.val < t0
  · rw [extF_lt _ _ _ h, extF_lt _ _ _ h]
  · have hj : t0 ≤ j.val := by omega
    have h1 := extF_ge t0 σ⁻¹ j hj
    have h2 : t0 ≤ (extF t0 σ⁻¹ j).val := by omega
    apply Fin.ext
    rw [extF_ge t0 σ _ h2]
    have e : (⟨(extF t0 σ⁻¹ j).val - t0, by have := (extF t0 σ⁻¹ j).isLt; omega⟩ : Fin (n - t0))
        = σ⁻¹ ⟨j.val - t0, by have := j.isLt; omega⟩ := by
      apply Fin.ext; simp only [h1]; omega
    rw [e]
    rw [← Equiv.Perm.mul_apply, mul_inv_cancel, Equiv.Perm.one_apply]
    show t0 + (j.val - t0) = j.val; omega

/-- The extended permutation. -/
def extPerm (t0 : ℕ) (σ : Equiv.Perm (Fin (n - t0))) : Equiv.Perm (Fin n) where
  toFun := extF t0 σ
  invFun := extF t0 σ⁻¹
  left_inv j := by have := extF_extF t0 σ⁻¹ j; rwa [inv_inv] at this
  right_inv j := extF_extF t0 σ j

theorem exists_sort_tail (g : Fin m → Pauli n) (t0 : ℕ) :
    ∃ τ : Equiv.Perm (Fin n), (∀ j : Fin n, j.val < t0 → τ j = j) ∧
      ∀ j l : Fin n, t0 ≤ j.val → j.val + 1 = l.val →
        colLe (synP (fun i => permP τ (g i)) j 0) (synP (fun i => permP τ (g i)) l 0) := by
  let f : Fin (n - t0) → Lex (Fin m → Bool) := fun i =>
    toLex (synP g ⟨t0 + i.val, by have := i.isLt; omega⟩ 0)
  let σ := Tuple.sort f
  have hmono : Monotone (f ∘ σ) := Tuple.monotone_sort f
  refine ⟨extPerm t0 σ, fun j hj => extF_lt t0 σ j hj, fun j l hj hl => ?_⟩
  rw [synP_permP, synP_permP, colLe_iff_toLex_le]
  have hjlt : j.val - t0 < n - t0 := by have := l.isLt; omega
  have hllt : l.val - t0 < n - t0 := by have := l.isLt; omega
  have ej : extPerm t0 σ j = ⟨t0 + (σ ⟨j.val - t0, hjlt⟩).val,
      by have := (σ ⟨j.val - t0, hjlt⟩).isLt; omega⟩ := Fin.ext (extF_ge t0 σ j hj)
  have el : extPerm t0 σ l = ⟨t0 + (σ ⟨l.val - t0, hllt⟩).val,
      by have := (σ ⟨l.val - t0, hllt⟩).isLt; omega⟩ := Fin.ext (extF_ge t0 σ l (by omega))
  have hle : (⟨j.val - t0, hjlt⟩ : Fin (n - t0)) ≤ ⟨l.val - t0, hllt⟩ := by
    rw [Fin.mk_le_mk]; omega
  have := hmono hle
  rw [ej, el]
  exact this

end LowWeight
