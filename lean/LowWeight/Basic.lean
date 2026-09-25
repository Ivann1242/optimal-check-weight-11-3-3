import LowWeight.Defs

/-! Basic algebra of the symplectic form and of the weight. -/

namespace LowWeight

variable {n : ℕ}

theorem symp_comm (u v : Pauli n) : symp u v = symp v u := by
  unfold symp; congr 1; ext j; ring

theorem symp_add_left (u u' v : Pauli n) : symp (u + u') v = symp u v + symp u' v := by
  unfold symp; rw [← Finset.sum_add_distrib]; congr 1; ext j; simp only [Pi.add_apply,
    Prod.fst_add, Prod.snd_add]; ring

theorem symp_add_right (u v v' : Pauli n) : symp u (v + v') = symp u v + symp u v' := by
  rw [symp_comm, symp_add_left, symp_comm v, symp_comm v']

theorem symp_smul_left (c : F) (u v : Pauli n) : symp (c • u) v = c * symp u v := by
  unfold symp; rw [Finset.mul_sum]; congr 1; ext j; simp only [Pi.smul_apply, Prod.smul_fst,
    Prod.smul_snd, smul_eq_mul]; ring

theorem symp_smul_right (c : F) (u v : Pauli n) : symp u (c • v) = c * symp u v := by
  rw [symp_comm, symp_smul_left, symp_comm]

@[simp] theorem symp_zero_left (v : Pauli n) : symp 0 v = 0 := by simp [symp]

@[simp] theorem symp_zero_right (v : Pauli n) : symp v 0 = 0 := by simp [symp]

/-- The symplectic form as a bilinear map. -/
def sympBil : Pauli n →ₗ[F] Pauli n →ₗ[F] F :=
  LinearMap.mk₂ F symp symp_add_left symp_smul_left symp_add_right symp_smul_right

@[simp] theorem sympBil_apply (u v : Pauli n) : sympBil u v = symp u v := rfl

/-- If `v` commutes with every generator, it commutes with their span. -/
theorem symp_eq_zero_of_mem_span {m : ℕ} {g : Fin m → Pauli n} {v s : Pauli n}
    (hv : ∀ i, symp v (g i) = 0) (hs : s ∈ Submodule.span F (Set.range g)) : symp v s = 0 := by
  induction hs using Submodule.span_induction with
  | mem x hx => obtain ⟨i, rfl⟩ := hx; exact hv i
  | zero => simp
  | add x y _ _ hx hy => rw [symp_add_right, hx, hy, add_zero]
  | smul c x _ hx => rw [symp_smul_right, hx, mul_zero]

/-- Elements of the span of pairwise commuting generators pairwise commute. -/
theorem symp_span_span {m : ℕ} {g : Fin m → Pauli n} (hc : ∀ i j, symp (g i) (g j) = 0)
    {s t : Pauli n} (hs : s ∈ Submodule.span F (Set.range g))
    (ht : t ∈ Submodule.span F (Set.range g)) : symp s t = 0 := by
  have : ∀ i, symp (g i) t = 0 := fun i => symp_eq_zero_of_mem_span (hc i) ht
  have h2 : ∀ i, symp t (g i) = 0 := fun i => by rw [symp_comm]; exact this i
  rw [symp_comm]; exact symp_eq_zero_of_mem_span h2 hs

theorem wt_le_card (v : Pauli n) : wt v ≤ n := by
  unfold wt; exact (Finset.card_filter_le _ _).trans (by simp)

theorem wt_zero : wt (0 : Pauli n) = 0 := by simp [wt]

theorem wt_pos_iff (v : Pauli n) : 0 < wt v ↔ v ≠ 0 := by
  unfold wt
  rw [Finset.card_pos, Finset.filter_nonempty_iff]
  constructor
  · rintro ⟨j, -, hj⟩ rfl; exact hj rfl
  · intro hv; by_contra h; push Not at h; exact hv (funext fun j => h j (Finset.mem_univ _))

end LowWeight
