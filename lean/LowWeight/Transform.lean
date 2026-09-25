import LowWeight.Basic

/-! Symmetries of the code conditions: qubit permutations and local (single-qubit) Clifford maps. -/

namespace LowWeight

variable {n : ℕ}

/-! ### A general invariance theorem -/

/-- Any weight- and symplectic-form-preserving linear automorphism maps codes to codes. -/
theorem IsCode.map_linearEquiv {m w : ℕ} {g : Fin m → Pauli n} (T : Pauli n ≃ₗ[F] Pauli n)
    (hwt : ∀ v, wt (T v) = wt v) (hsymp : ∀ u v, symp (T u) (T v) = symp u v)
    (h : IsCode n m w g) : IsCode n m w (fun i => T (g i)) := by
  obtain ⟨hli, hw, hc, hd⟩ := h
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact hli.map_injOn T.toLinearMap (T.injective.injOn)
  · intro i; rw [hwt]; exact hw i
  · intro i j; rw [hsymp]; exact hc i j
  · intro v h1 h2 hv
    have hTv : T (T.symm v) = v := T.apply_symm_apply v
    have hw' : wt (T.symm v) = wt v := by rw [← hwt, hTv]
    have hmem : T.symm v ∈ Submodule.span F (Set.range g) := by
      refine hd _ (by rw [hw']; exact h1) (by rw [hw']; exact h2) fun i => ?_
      rw [← hsymp, hTv]; exact hv i
    have := Submodule.mem_map_of_mem (f := T.toLinearMap) hmem
    rw [Submodule.map_span, ← Set.range_comp] at this
    simpa [hTv, Function.comp_def] using this

/-! ### Qubit permutations -/

/-- Relabel the qubits by a permutation: `(permP σ v) j = v (σ j)`. -/
def permP (σ : Equiv.Perm (Fin n)) : Pauli n ≃ₗ[F] Pauli n :=
  LinearEquiv.funCongrLeft F (F × F) σ

@[simp] theorem permP_apply (σ : Equiv.Perm (Fin n)) (v : Pauli n) (j : Fin n) :
    permP σ v j = v (σ j) := rfl

theorem wt_permP (σ : Equiv.Perm (Fin n)) (v : Pauli n) : wt (permP σ v) = wt v := by
  unfold wt
  refine Finset.card_bij' (fun j _ => σ j) (fun j _ => σ.symm j) ?_ ?_ ?_ ?_
  · intro j hj
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp hj).2⟩
  · intro j hj
    refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
    show v (σ (σ.symm j)) ≠ 0
    rw [Equiv.apply_symm_apply]; exact (Finset.mem_filter.mp hj).2
  · intro j _; simp
  · intro j _; simp

theorem symp_permP (σ : Equiv.Perm (Fin n)) (u v : Pauli n) :
    symp (permP σ u) (permP σ v) = symp u v := by
  unfold symp
  exact Equiv.sum_comp σ (fun j => (u j).1 * (v j).2 + (u j).2 * (v j).1)

theorem IsCode.perm {m w : ℕ} {g : Fin m → Pauli n} (σ : Equiv.Perm (Fin n))
    (h : IsCode n m w g) : IsCode n m w (fun i => permP σ (g i)) :=
  h.map_linearEquiv (permP σ) (wt_permP σ) (symp_permP σ)

/-! ### Local maps -/

/-- The single-qubit symplectic form. -/
def ω (p q : F × F) : F := p.1 * q.2 + p.2 * q.1

private theorem omega_basis_aux (a b : F × F) (ha : a ≠ 0) (hb : b ≠ 0) (hab : a ≠ b) :
    a.1 * b.2 + a.2 * b.1 = 1 := by
  obtain ⟨a1, a2⟩ := a
  obtain ⟨b1, b2⟩ := b
  revert ha hb hab
  revert a1 a2 b1 b2
  decide

/-- Over `ZMod 2`, every invertible linear map of `F × F` preserves `ω`. -/
theorem omega_linearEquiv (M : (F × F) ≃ₗ[F] (F × F)) (p q : F × F) :
    ω (M p) (M q) = ω p q := by
  set a := M (1, 0)
  set b := M (0, 1)
  have ha : a ≠ 0 := by
    intro h; have := M.injective (h.trans M.map_zero.symm); simp at this
  have hb : b ≠ 0 := by
    intro h; have := M.injective (h.trans M.map_zero.symm); simp at this
  have hab' : a ≠ b := by
    intro h; have := M.injective h; simp at this
  have hab := omega_basis_aux a b ha hb hab'
  have hdec : ∀ x : F × F, M x = x.1 • a + x.2 • b := by
    intro x
    have : x = x.1 • ((1 : F), (0 : F)) + x.2 • ((0 : F), (1 : F)) := by ext <;> simp
    conv_lhs => rw [this]
    rw [map_add, map_smul, map_smul]
  have h2 : (2 : F) = 0 := rfl
  rw [hdec p, hdec q]
  unfold ω
  simp only [Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
  linear_combination (p.1 * q.2 + p.2 * q.1) * hab +
    (p.1 * q.1 * a.1 * a.2 + p.2 * q.2 * b.1 * b.2) * h2

/-- Apply an invertible linear map `M j` on each qubit `j`. -/
def localP (M : Fin n → (F × F) ≃ₗ[F] (F × F)) : Pauli n ≃ₗ[F] Pauli n :=
  LinearEquiv.piCongrRight M

@[simp] theorem localP_apply (M : Fin n → (F × F) ≃ₗ[F] (F × F)) (v : Pauli n) (j : Fin n) :
    localP M v j = M j (v j) := rfl

theorem wt_localP (M : Fin n → (F × F) ≃ₗ[F] (F × F)) (v : Pauli n) :
    wt (localP M v) = wt v := by
  unfold wt
  congr 1
  apply Finset.filter_congr
  intro j _
  simp

theorem symp_localP (M : Fin n → (F × F) ≃ₗ[F] (F × F)) (u v : Pauli n) :
    symp (localP M u) (localP M v) = symp u v := by
  unfold symp
  refine Finset.sum_congr rfl fun j _ => ?_
  exact omega_linearEquiv (M j) (u j) (v j)

theorem IsCode.localMap {m w : ℕ} {g : Fin m → Pauli n} (M : Fin n → (F × F) ≃ₗ[F] (F × F))
    (h : IsCode n m w g) : IsCode n m w (fun i => localP M (g i)) :=
  h.map_linearEquiv (localP M) (wt_localP M) (symp_localP M)

end LowWeight
