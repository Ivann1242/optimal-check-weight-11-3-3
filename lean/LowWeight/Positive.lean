import LowWeight.Bridge

/-! An explicit `[[12, 3, 3]]` stabilizer code with 9 generators of weight 4 (pure, distance 3). -/

namespace LowWeight

namespace Code12

def pI : F × F := (0, 0)
def pX : F × F := (1, 0)
def pZ : F × F := (0, 1)
def pY : F × F := (1, 1)

/-- The generators; row `i` is generator `i`, entry `j` its Pauli on qubit `j`. -/
def gen : Fin 9 → Pauli 12 :=
  ![![pI, pI, pI, pI, pI, pI, pZ, pZ, pI, pI, pZ, pZ],
    ![pI, pI, pI, pI, pI, pI, pI, pI, pZ, pZ, pX, pX],
    ![pZ, pZ, pI, pI, pI, pI, pI, pI, pX, pX, pI, pI],
    ![pI, pI, pI, pI, pZ, pZ, pX, pX, pI, pI, pI, pI],
    ![pI, pI, pI, pZ, pI, pX, pI, pY, pI, pI, pI, pX],
    ![pZ, pI, pZ, pI, pX, pX, pI, pI, pI, pI, pI, pI],
    ![pI, pZ, pX, pX, pI, pZ, pI, pI, pI, pI, pI, pI],
    ![pI, pX, pI, pY, pI, pI, pI, pI, pI, pY, pI, pZ],
    ![pX, pI, pI, pI, pY, pI, pZ, pI, pZ, pI, pI, pI]]

/-- Symplectic duals: `symp (dual k) (gen i) = δ_ki`. -/
def dual : Fin 9 → Pauli 12 :=
  ![![pZ, pI, pI, pI, pI, pI, pX, pI, pI, pI, pI, pI],
    ![pZ, pI, pI, pI, pI, pI, pI, pI, pX, pI, pI, pI],
    ![pX, pI, pX, pI, pI, pI, pI, pI, pI, pI, pI, pI],
    ![pZ, pI, pI, pI, pX, pI, pI, pI, pI, pI, pI, pI],
    ![pI, pZ, pI, pX, pI, pI, pI, pI, pI, pI, pI, pI],
    ![pI, pI, pX, pI, pI, pI, pI, pI, pI, pI, pI, pI],
    ![pX, pX, pX, pI, pI, pI, pI, pI, pI, pI, pI, pI],
    ![pI, pZ, pI, pI, pI, pI, pI, pI, pI, pI, pI, pI],
    ![pZ, pI, pI, pI, pI, pI, pI, pI, pI, pI, pI, pI]]

theorem gen_wt : ∀ i, wt (gen i) ≤ 4 := by decide +kernel

theorem gen_symp : ∀ i j, symp (gen i) (gen j) = 0 := by decide +kernel

theorem dual_symp : ∀ k i, symp (dual k) (gen i) = if i = k then 1 else 0 := by decide +kernel

theorem linInd_of_dual {m n : ℕ} (g d : Fin m → Pauli n)
    (hd : ∀ k i, symp (d k) (g i) = if i = k then 1 else 0) : LinearIndependent F g := by
  refine (@Fintype.linearIndependent_iff (Fin m) F (Pauli n) _ _ (inferInstance : Module F (Pauli n)) _ _).mpr ?_
  intro c hc k
  have h := congrArg (sympBil (d k)) hc
  rw [map_sum, map_zero] at h
  simp only [map_smul, sympBil_apply, hd, smul_eq_mul, mul_ite, mul_one, mul_zero,
    Finset.sum_ite_eq', Finset.mem_univ, ite_true] at h
  exact h

theorem gen_linInd : LinearIndependent F gen := linInd_of_dual gen dual dual_symp

/-- Local syndrome of `p` on qubit `j` against generator `i`. -/
def loc (p : F × F) (j : Fin 12) (i : Fin 9) : F := p.1 * (gen i j).2 + p.2 * (gen i j).1

theorem single_check : ∀ j : Fin 12, ∀ p : F × F, p ≠ 0 → ∃ i, loc p j i ≠ 0 := by
  decide +kernel

theorem pair_check : ∀ j l : Fin 12, j ≠ l → ∀ p q : F × F, p ≠ 0 → q ≠ 0 →
    ∃ i, loc p j i + loc q l i ≠ 0 := by
  decide +kernel

theorem no_low (v : Pauli 12) (h1 : 1 ≤ wt v) (h2 : wt v ≤ 2)
    (hv : ∀ i, symp v (gen i) = 0) : False := by
  set S := Finset.univ.filter fun j => v j ≠ 0 with hS
  have hmem : ∀ q, q ∈ S ↔ v q ≠ 0 := fun q => by simp [hS]
  have h1' : 1 ≤ S.card := h1
  have h2' : S.card ≤ 2 := h2
  have hcard : S.card = 1 ∨ S.card = 2 := by omega
  rcases hcard with hc | hc
  · obtain ⟨j, hj⟩ := Finset.card_eq_one.mp hc
    have hvj : v j ≠ 0 := (hmem j).mp (by simp [hj])
    have hveq : v = Pi.single j (v j) := by
      funext q
      by_cases hq : q = j
      · subst hq; simp
      · have : q ∉ S := by simp [hj, hq]
        rw [hmem, not_not] at this
        simp [hq, this]
    obtain ⟨i, hi⟩ := single_check j (v j) hvj
    apply hi
    have := hv i
    rw [hveq, symp_single] at this
    exact this
  · obtain ⟨j, l, hjl, hj⟩ := Finset.card_eq_two.mp hc
    have hvj : v j ≠ 0 := (hmem j).mp (by simp [hj])
    have hvl : v l ≠ 0 := (hmem l).mp (by simp [hj])
    have hveq : v = Pi.single j (v j) + Pi.single l (v l) := by
      funext q
      by_cases hq : q = j
      · subst hq; simp [hjl]
      · by_cases hql : q = l
        · subst hql; simp [hq]
        · have : q ∉ S := by simp [hj, hq, hql]
          rw [hmem, not_not] at this
          simp [hq, hql, this]
    obtain ⟨i, hi⟩ := pair_check j l hjl (v j) (v l) hvj hvl
    apply hi
    have := hv i
    rw [hveq, symp_add_left, symp_single, symp_single] at this
    exact this

end Code12

open Code12 in
theorem exists_code_12 : ∃ g : Fin 9 → Pauli 12, IsCode 12 9 4 g :=
  ⟨gen, gen_linInd, gen_wt, gen_symp, fun v h1 h2 hv => (no_low v h1 h2 hv).elim⟩

end LowWeight
