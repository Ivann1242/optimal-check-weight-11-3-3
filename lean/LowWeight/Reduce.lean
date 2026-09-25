import LowWeight.Basic

/-! Base case and weight-one reduction. -/

namespace LowWeight

theorem not_isCode_zero {n w : ℕ} (hn : 1 ≤ n) (g : Fin 0 → Pauli n) : ¬ IsCode n 0 w g := by
  intro h
  let v : Pauli n := fun j => if j = ⟨0, hn⟩ then (1, 0) else 0
  have hwt : wt v = 1 := by
    unfold wt
    rw [Finset.card_eq_one]
    refine ⟨⟨0, hn⟩, ?_⟩
    ext j
    by_cases hj : j = ⟨0, hn⟩ <;> simp [v, hj]
  have hmem := h.2.2.2 v (by omega) (by omega) (fun i => i.elim0)
  rw [Set.range_eq_empty, Submodule.span_empty, Submodule.mem_bot] at hmem
  have := congrFun hmem ⟨0, hn⟩
  simp [v] at this

section Reduce

variable {n : ℕ}

/-- Restriction to the qubits other than `j0`. -/
def restr (j0 : Fin (n+1)) : Pauli (n+1) →ₗ[F] Pauli n :=
  LinearMap.funLeft F (F × F) j0.succAbove

@[simp] theorem restr_apply (j0 : Fin (n+1)) (u : Pauli (n+1)) (k : Fin n) :
    restr j0 u k = u (j0.succAbove k) := rfl

/-- Single-qubit symplectic form. -/
def om (p q : F × F) : F := p.1 * q.2 + p.2 * q.1

theorem symp_split (j0 : Fin (n+1)) (u v : Pauli (n+1)) :
    symp u v = om (u j0) (v j0) + symp (restr j0 u) (restr j0 v) := by
  unfold symp om
  rw [Fin.sum_univ_succAbove _ j0]
  rfl

theorem wt_split (j0 : Fin (n+1)) (u : Pauli (n+1)) :
    wt u = (if u j0 ≠ 0 then 1 else 0) + wt (restr j0 u) := by
  unfold wt
  rw [Finset.card_filter, Finset.card_filter, Fin.sum_univ_succAbove _ j0]
  rfl

theorem ext_split (j0 : Fin (n+1)) {u u' : Pauli (n+1)} (h0 : u j0 = u' j0)
    (h : restr j0 u = restr j0 u') : u = u' := by
  funext j
  rcases Fin.eq_self_or_eq_succAbove j0 j with rfl | ⟨k, rfl⟩
  · exact h0
  · exact congrFun h k

theorem om_pair : ∀ p q : F × F, p ≠ 0 → om q p = 0 → q = 0 ∨ q = p := by
  unfold om; decide

theorem om_zero_left (q : F × F) : om 0 q = 0 := by simp [om]

theorem om_zero_right (q : F × F) : om q 0 = 0 := by simp [om]

theorem om_self : ∀ q : F × F, om q q = 0 := by unfold om; decide

end Reduce

/-- Work around a unification failure between `Pi.addCommMonoid` and
`AddCommGroup.toAddCommMonoid Pi.addCommGroup` during instance synthesis. -/
local instance instModulePauliGrp {k : ℕ} : @Module F (Pauli k) _ AddCommGroup.toAddCommMonoid :=
  (inferInstance : Module F (Pauli k))

local instance instModuleFinFunGrp {k : ℕ} : @Module F (Fin k → F) _ AddCommGroup.toAddCommMonoid :=
  (inferInstance : Module F (Fin k → F))

theorem IsCode.reduce_weight_one {n m w : ℕ} {g : Fin (m+1) → Pauli (n+1)}
    (hg : IsCode (n+1) (m+1) w g)
    (e : Pauli (n+1)) (he : e ∈ Submodule.span F (Set.range g)) (hwe : wt e = 1) :
    ∃ h : Fin m → Pauli n, IsCode n m w h := by
  obtain ⟨hli, hwg, hcg, hdg⟩ := hg
  set S := Submodule.span F (Set.range g) with hS
  obtain ⟨j0, hj0⟩ : ∃ j0, Finset.univ.filter (fun j => e j ≠ 0) = {j0} :=
    Finset.card_eq_one.mp hwe
  have hej0 : e j0 ≠ 0 := by
    have : j0 ∈ Finset.univ.filter (fun j => e j ≠ 0) := by
      rw [hj0]; exact Finset.mem_singleton_self _
    simpa using this
  have heoff : ∀ j, j ≠ j0 → e j = 0 := by
    intro j hj
    by_contra hne
    have : j ∈ Finset.univ.filter (fun j => e j ≠ 0) := by simpa using hne
    rw [hj0, Finset.mem_singleton] at this
    exact hj this
  have hπe : restr j0 e = 0 := by
    funext k; exact heoff _ (Fin.succAbove_ne j0 k)
  have hSj0 : ∀ s ∈ S, s j0 = 0 ∨ s j0 = e j0 := by
    intro s hs
    have h1 := symp_span_span hcg hs he
    rw [symp_split j0, hπe, symp_zero_right, add_zero] at h1
    exact om_pair _ _ hej0 h1
  have hSsymp : ∀ s ∈ S, ∀ t ∈ S, symp (restr j0 s) (restr j0 t) = 0 := by
    intro s hs t ht
    have h1 := symp_span_span hcg hs ht
    rw [symp_split j0] at h1
    have h2 : om (s j0) (t j0) = 0 := by
      rcases hSj0 s hs with h | h <;> rcases hSj0 t ht with h' | h' <;> rw [h, h'] <;>
        first | exact om_zero_left _ | exact om_zero_right _ | exact om_self _
    rw [h2, zero_add] at h1; exact h1
  let L := Fintype.linearCombination F g
  have hL : ∀ c, L c = ∑ i, c i • g i := fun c => Fintype.linearCombination_apply F g c
  have hLinj : ∀ c c', L c = L c' → c = c' := by
    intro c c' hcc
    have h0 : L (c - c') = 0 := by rw [map_sub, hcc]; exact sub_self _
    rw [hL] at h0
    have := Fintype.linearIndependent_iff.mp hli _ h0
    funext i; exact sub_eq_zero.mp (this i)
  have hLS : ∀ c, L c ∈ S := by
    intro c
    rw [hS, ← Fintype.range_linearCombination]; exact LinearMap.mem_range_self _ _
  obtain ⟨c0, hc0⟩ : e ∈ LinearMap.range L := by
    rw [Fintype.range_linearCombination]; exact he
  let f : (Fin (m+1) → F) →ₗ[F] Pauli n := (restr j0).comp L
  have hker : LinearMap.ker f = Submodule.span F {c0} := by
    apply le_antisymm
    · intro x hx
      rw [LinearMap.mem_ker] at hx
      have hx' : restr j0 (L x) = 0 := hx
      rw [Submodule.mem_span_singleton]
      rcases hSj0 (L x) (hLS x) with h0 | h0
      · refine ⟨0, ?_⟩
        rw [zero_smul]
        apply hLinj
        rw [map_zero]
        exact ext_split j0 (by rw [h0]; rfl) (by rw [hx', map_zero])
      · refine ⟨1, ?_⟩
        rw [one_smul]
        apply hLinj
        rw [hc0]
        exact ext_split j0 h0.symm (by rw [hx', hπe])
    · rw [Submodule.span_le, Set.singleton_subset_iff]
      show restr j0 (L c0) = 0
      rw [hc0]; exact hπe
  have hne : c0 ≠ 0 := by
    rintro rfl; apply hej0; rw [← hc0, map_zero]; rfl
  have hrank := LinearMap.finrank_range_add_finrank_ker f
  have hrank' : Module.finrank F (LinearMap.range f) + 1 = m + 1 := by
    have hk : Module.finrank F (LinearMap.ker f) = 1 := by
      rw [hker]; exact finrank_span_singleton hne
    convert hrank using 2
    · rfl
    · exact hk.symm
    · exact (Module.finrank_fin_fun F).symm
  have hrange : LinearMap.range f = S.map (restr j0) := by
    rw [LinearMap.range_comp, Fintype.range_linearCombination]
  have hmapS : S.map (restr j0) = Submodule.span F (Set.range (restr j0 ∘ g)) := by
    rw [hS, Submodule.map_span, ← Set.range_comp]
  have hT : Module.finrank F (Submodule.span F (Set.range (restr j0 ∘ g))) = m := by
    rw [← hmapS, ← hrange]; omega
  obtain ⟨b, hbsub, hbspan, hbli⟩ := exists_linearIndependent F (Set.range (restr j0 ∘ g))
  have hbfin : b.Finite := (Set.finite_range _).subset hbsub
  have : Fintype b := hbfin.fintype
  have hcard : Fintype.card b = m := by
    have := finrank_span_eq_card hbli
    rw [Subtype.range_coe, hbspan] at this
    exact this.symm.trans hT
  let σ : Fin m ≃ b := (Fintype.equivFinOfCardEq hcard).symm
  let h : Fin m → Pauli n := fun i => (σ i).1
  have hrh : Set.range h = b := by
    ext x; constructor
    · rintro ⟨i, rfl⟩; exact (σ i).2
    · intro hx; exact ⟨σ.symm ⟨x, hx⟩, by simp [h]⟩
  have hspan : Submodule.span F (Set.range h) = S.map (restr j0) := by
    rw [hrh]; exact hbspan.trans hmapS.symm
  have hhg : ∀ i, ∃ k, h i = restr j0 (g k) := by
    intro i
    obtain ⟨k, hk⟩ := hbsub (σ i).2
    exact ⟨k, hk.symm⟩
  refine ⟨h, hbli.comp σ σ.injective, ?_, ?_, ?_⟩
  · intro i
    obtain ⟨k, hk⟩ := hhg i
    rw [hk]
    have := wt_split j0 (g k)
    have := hwg k
    omega
  · intro i j
    obtain ⟨k, hk⟩ := hhg i
    obtain ⟨l, hl⟩ := hhg j
    rw [hk, hl]
    exact hSsymp _ (Submodule.subset_span ⟨k, rfl⟩) _ (Submodule.subset_span ⟨l, rfl⟩)
  · intro v' h1 h2 hv'
    let v : Pauli (n+1) := Fin.insertNth (α := fun _ => F × F) j0 0 v'
    have hv0 : v j0 = 0 := by simp [v]
    have hπv : restr j0 v = v' := by
      funext k; simp [v]
    have hwv : wt v = wt v' := by
      rw [wt_split j0, hv0, hπv]; simp
    have hcomm : ∀ i, symp v (g i) = 0 := by
      intro i
      rw [symp_split j0, hv0, om_zero_left, zero_add, hπv]
      apply symp_eq_zero_of_mem_span hv'
      rw [hspan]
      exact Submodule.mem_map_of_mem (Submodule.subset_span ⟨i, rfl⟩)
    have hvS : v ∈ S := hdg v (by omega) (by omega) hcomm
    rw [hspan, ← hπv]
    exact Submodule.mem_map_of_mem hvS

end LowWeight
