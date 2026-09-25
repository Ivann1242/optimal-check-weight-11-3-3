import LowWeight.Positive

/-! Further explicit pure distance-3 stabilizer codes with low-weight generators. -/

namespace LowWeight

/-- Local syndrome of the single-qubit Pauli `p` on qubit `j` against generator `i` of `g`. -/
def locG {n m : ℕ} (g : Fin m → Pauli n) (p : F × F) (j : Fin n) (i : Fin m) : F :=
  p.1 * (g i j).2 + p.2 * (g i j).1

/-- Generic form of `Code12.no_low`: finite single/pair syndrome checks rule out any
weight-1 or weight-2 operator commuting with all generators. -/
theorem no_low_of_checks {n m : ℕ} (g : Fin m → Pauli n)
    (single_check : ∀ j : Fin n, ∀ p : F × F, p ≠ 0 → ∃ i, locG g p j i ≠ 0)
    (pair_check : ∀ j l : Fin n, j ≠ l → ∀ p q : F × F, p ≠ 0 → q ≠ 0 →
      ∃ i, locG g p j i + locG g q l i ≠ 0)
    (v : Pauli n) (h1 : 1 ≤ wt v) (h2 : wt v ≤ 2)
    (hv : ∀ i, symp v (g i) = 0) : False := by
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

/-- Packaging: duals, weight and commutation checks, and syndrome checks give `IsCode`. -/
theorem isCode_of_checks {n m w : ℕ} (g d : Fin m → Pauli n)
    (hd : ∀ k i, symp (d k) (g i) = if i = k then 1 else 0)
    (hw : ∀ i, wt (g i) ≤ w) (hc : ∀ i j, symp (g i) (g j) = 0)
    (hs : ∀ j : Fin n, ∀ p : F × F, p ≠ 0 → ∃ i, locG g p j i ≠ 0)
    (hp : ∀ j l : Fin n, j ≠ l → ∀ p q : F × F, p ≠ 0 → q ≠ 0 →
      ∃ i, locG g p j i + locG g q l i ≠ 0) : IsCode n m w g :=
  ⟨Code12.linInd_of_dual g d hd, hw, hc, fun v h1 h2 hv => (no_low_of_checks g hs hp v h1 h2 hv).elim⟩

namespace Code10_4

def gen : Fin 6 → Pauli 10 :=
  ![![Code12.pI, Code12.pZ, Code12.pI, Code12.pZ, Code12.pI, Code12.pZ, Code12.pZ, Code12.pZ, Code12.pI, Code12.pZ],
    ![Code12.pI, Code12.pI, Code12.pI, Code12.pZ, Code12.pZ, Code12.pZ, Code12.pI, Code12.pZ, Code12.pZ, Code12.pZ],
    ![Code12.pZ, Code12.pI, Code12.pI, Code12.pI, Code12.pI, Code12.pX, Code12.pX, Code12.pX, Code12.pX, Code12.pX],
    ![Code12.pZ, Code12.pI, Code12.pZ, Code12.pX, Code12.pX, Code12.pI, Code12.pI, Code12.pI, Code12.pY, Code12.pY],
    ![Code12.pZ, Code12.pX, Code12.pX, Code12.pZ, Code12.pX, Code12.pI, Code12.pI, Code12.pX, Code12.pI, Code12.pI],
    ![Code12.pX, Code12.pI, Code12.pY, Code12.pI, Code12.pX, Code12.pZ, Code12.pY, Code12.pI, Code12.pI, Code12.pY]]

def dual : Fin 6 → Pauli 10 :=
  ![![Code12.pI, Code12.pX, Code12.pI, Code12.pI, Code12.pI, Code12.pI, Code12.pI, Code12.pI, Code12.pI, Code12.pI],
    ![Code12.pI, Code12.pI, Code12.pI, Code12.pI, Code12.pX, Code12.pI, Code12.pI, Code12.pI, Code12.pI, Code12.pI],
    ![Code12.pX, Code12.pI, Code12.pX, Code12.pX, Code12.pI, Code12.pX, Code12.pI, Code12.pI, Code12.pI, Code12.pI],
    ![Code12.pI, Code12.pX, Code12.pX, Code12.pI, Code12.pX, Code12.pX, Code12.pI, Code12.pI, Code12.pI, Code12.pI],
    ![Code12.pI, Code12.pX, Code12.pI, Code12.pX, Code12.pX, Code12.pI, Code12.pI, Code12.pI, Code12.pI, Code12.pI],
    ![Code12.pI, Code12.pX, Code12.pI, Code12.pI, Code12.pX, Code12.pX, Code12.pI, Code12.pI, Code12.pI, Code12.pI]]

theorem gen_wt : ∀ i, wt (gen i) ≤ 6 := by decide +kernel

theorem gen_symp : ∀ i j, symp (gen i) (gen j) = 0 := by decide +kernel

theorem dual_symp : ∀ k i, symp (dual k) (gen i) = if i = k then 1 else 0 := by decide +kernel

theorem single_check : ∀ j : Fin 10, ∀ p : F × F, p ≠ 0 → ∃ i, locG gen p j i ≠ 0 := by
  decide +kernel

theorem pair_check : ∀ j l : Fin 10, j ≠ l → ∀ p q : F × F, p ≠ 0 → q ≠ 0 →
    ∃ i, locG gen p j i + locG gen q l i ≠ 0 := by
  decide +kernel

end Code10_4

theorem exists_code_10_4 : ∃ g : Fin 6 → Pauli 10, IsCode 10 6 6 g :=
  ⟨Code10_4.gen, isCode_of_checks _ Code10_4.dual Code10_4.dual_symp Code10_4.gen_wt Code10_4.gen_symp
    Code10_4.single_check Code10_4.pair_check⟩

namespace Code11_4

def gen : Fin 7 → Pauli 11 :=
  ![![Code12.pZ, Code12.pI, Code12.pZ, Code12.pZ, Code12.pI, Code12.pI, Code12.pI, Code12.pI, Code12.pI, Code12.pZ, Code12.pZ],
    ![Code12.pI, Code12.pZ, Code12.pI, Code12.pZ, Code12.pI, Code12.pI, Code12.pZ, Code12.pZ, Code12.pZ, Code12.pI, Code12.pI],
    ![Code12.pZ, Code12.pI, Code12.pI, Code12.pI, Code12.pZ, Code12.pZ, Code12.pI, Code12.pZ, Code12.pI, Code12.pZ, Code12.pI],
    ![Code12.pI, Code12.pI, Code12.pI, Code12.pI, Code12.pI, Code12.pI, Code12.pZ, Code12.pX, Code12.pX, Code12.pX, Code12.pX],
    ![Code12.pI, Code12.pI, Code12.pI, Code12.pX, Code12.pX, Code12.pX, Code12.pX, Code12.pI, Code12.pI, Code12.pI, Code12.pY],
    ![Code12.pI, Code12.pX, Code12.pX, Code12.pI, Code12.pI, Code12.pX, Code12.pX, Code12.pI, Code12.pI, Code12.pY, Code12.pI],
    ![Code12.pX, Code12.pI, Code12.pY, Code12.pI, Code12.pY, Code12.pI, Code12.pY, Code12.pI, Code12.pY, Code12.pI, Code12.pI]]

def dual : Fin 7 → Pauli 11 :=
  ![![Code12.pI, Code12.pX, Code12.pI, Code12.pX, Code12.pI, Code12.pI, Code12.pI, Code12.pI, Code12.pI, Code12.pI, Code12.pI],
    ![Code12.pI, Code12.pX, Code12.pI, Code12.pI, Code12.pI, Code12.pI, Code12.pI, Code12.pI, Code12.pI, Code12.pI, Code12.pI],
    ![Code12.pX, Code12.pX, Code12.pI, Code12.pX, Code12.pI, Code12.pI, Code12.pI, Code12.pI, Code12.pI, Code12.pI, Code12.pI],
    ![Code12.pI, Code12.pI, Code12.pX, Code12.pX, Code12.pI, Code12.pI, Code12.pX, Code12.pI, Code12.pI, Code12.pI, Code12.pI],
    ![Code12.pI, Code12.pX, Code12.pI, Code12.pX, Code12.pI, Code12.pI, Code12.pI, Code12.pI, Code12.pI, Code12.pI, Code12.pX],
    ![Code12.pX, Code12.pI, Code12.pI, Code12.pI, Code12.pI, Code12.pI, Code12.pI, Code12.pI, Code12.pI, Code12.pX, Code12.pI],
    ![Code12.pI, Code12.pX, Code12.pX, Code12.pX, Code12.pI, Code12.pI, Code12.pI, Code12.pI, Code12.pI, Code12.pI, Code12.pI]]

theorem gen_wt : ∀ i, wt (gen i) ≤ 5 := by decide +kernel

theorem gen_symp : ∀ i j, symp (gen i) (gen j) = 0 := by decide +kernel

theorem dual_symp : ∀ k i, symp (dual k) (gen i) = if i = k then 1 else 0 := by decide +kernel

theorem single_check : ∀ j : Fin 11, ∀ p : F × F, p ≠ 0 → ∃ i, locG gen p j i ≠ 0 := by
  decide +kernel

theorem pair_check : ∀ j l : Fin 11, j ≠ l → ∀ p q : F × F, p ≠ 0 → q ≠ 0 →
    ∃ i, locG gen p j i + locG gen q l i ≠ 0 := by
  decide +kernel

end Code11_4

theorem exists_code_11_4 : ∃ g : Fin 7 → Pauli 11, IsCode 11 7 5 g :=
  ⟨Code11_4.gen, isCode_of_checks _ Code11_4.dual Code11_4.dual_symp Code11_4.gen_wt Code11_4.gen_symp
    Code11_4.single_check Code11_4.pair_check⟩

namespace Code11_5

def gen : Fin 6 → Pauli 11 :=
  ![![Code12.pI, Code12.pI, Code12.pI, Code12.pZ, Code12.pI, Code12.pZ, Code12.pZ, Code12.pZ, Code12.pZ, Code12.pZ, Code12.pZ],
    ![Code12.pI, Code12.pZ, Code12.pZ, Code12.pI, Code12.pZ, Code12.pI, Code12.pI, Code12.pX, Code12.pX, Code12.pX, Code12.pX],
    ![Code12.pI, Code12.pI, Code12.pI, Code12.pX, Code12.pX, Code12.pX, Code12.pX, Code12.pI, Code12.pY, Code12.pX, Code12.pX],
    ![Code12.pI, Code12.pX, Code12.pX, Code12.pI, Code12.pI, Code12.pY, Code12.pX, Code12.pZ, Code12.pI, Code12.pX, Code12.pY],
    ![Code12.pZ, Code12.pI, Code12.pX, Code12.pI, Code12.pY, Code12.pZ, Code12.pY, Code12.pY, Code12.pI, Code12.pZ, Code12.pI],
    ![Code12.pX, Code12.pY, Code12.pI, Code12.pI, Code12.pY, Code12.pY, Code12.pY, Code12.pI, Code12.pY, Code12.pI, Code12.pY]]

def dual : Fin 6 → Pauli 11 :=
  ![![Code12.pI, Code12.pI, Code12.pI, Code12.pX, Code12.pI, Code12.pI, Code12.pI, Code12.pI, Code12.pI, Code12.pI, Code12.pI],
    ![Code12.pI, Code12.pI, Code12.pX, Code12.pI, Code12.pI, Code12.pI, Code12.pI, Code12.pI, Code12.pI, Code12.pI, Code12.pI],
    ![Code12.pI, Code12.pX, Code12.pX, Code12.pX, Code12.pI, Code12.pI, Code12.pI, Code12.pI, Code12.pX, Code12.pI, Code12.pI],
    ![Code12.pX, Code12.pX, Code12.pX, Code12.pX, Code12.pI, Code12.pX, Code12.pI, Code12.pI, Code12.pI, Code12.pI, Code12.pI],
    ![Code12.pX, Code12.pI, Code12.pI, Code12.pI, Code12.pI, Code12.pI, Code12.pI, Code12.pI, Code12.pI, Code12.pI, Code12.pI],
    ![Code12.pI, Code12.pX, Code12.pX, Code12.pI, Code12.pI, Code12.pI, Code12.pI, Code12.pI, Code12.pI, Code12.pI, Code12.pI]]

theorem gen_wt : ∀ i, wt (gen i) ≤ 7 := by decide +kernel

theorem gen_symp : ∀ i j, symp (gen i) (gen j) = 0 := by decide +kernel

theorem dual_symp : ∀ k i, symp (dual k) (gen i) = if i = k then 1 else 0 := by decide +kernel

theorem single_check : ∀ j : Fin 11, ∀ p : F × F, p ≠ 0 → ∃ i, locG gen p j i ≠ 0 := by
  decide +kernel

theorem pair_check : ∀ j l : Fin 11, j ≠ l → ∀ p q : F × F, p ≠ 0 → q ≠ 0 →
    ∃ i, locG gen p j i + locG gen q l i ≠ 0 := by
  decide +kernel

end Code11_5

theorem exists_code_11_5 : ∃ g : Fin 6 → Pauli 11, IsCode 11 6 7 g :=
  ⟨Code11_5.gen, isCode_of_checks _ Code11_5.dual Code11_5.dual_symp Code11_5.gen_wt Code11_5.gen_symp
    Code11_5.single_check Code11_5.pair_check⟩

namespace Code12_4

def gen : Fin 8 → Pauli 12 :=
  ![![Code12.pI, Code12.pI, Code12.pI, Code12.pI, Code12.pI, Code12.pI, Code12.pI, Code12.pZ, Code12.pZ, Code12.pZ, Code12.pZ, Code12.pZ],
    ![Code12.pI, Code12.pI, Code12.pI, Code12.pZ, Code12.pI, Code12.pI, Code12.pI, Code12.pI, Code12.pX, Code12.pX, Code12.pX, Code12.pX],
    ![Code12.pI, Code12.pI, Code12.pI, Code12.pI, Code12.pZ, Code12.pZ, Code12.pZ, Code12.pX, Code12.pI, Code12.pI, Code12.pI, Code12.pX],
    ![Code12.pI, Code12.pI, Code12.pI, Code12.pX, Code12.pX, Code12.pX, Code12.pX, Code12.pI, Code12.pI, Code12.pI, Code12.pI, Code12.pZ],
    ![Code12.pI, Code12.pZ, Code12.pZ, Code12.pZ, Code12.pI, Code12.pY, Code12.pX, Code12.pI, Code12.pI, Code12.pI, Code12.pI, Code12.pI],
    ![Code12.pI, Code12.pX, Code12.pX, Code12.pI, Code12.pI, Code12.pI, Code12.pI, Code12.pI, Code12.pI, Code12.pZ, Code12.pZ, Code12.pI],
    ![Code12.pZ, Code12.pI, Code12.pZ, Code12.pI, Code12.pX, Code12.pI, Code12.pI, Code12.pY, Code12.pI, Code12.pI, Code12.pX, Code12.pI],
    ![Code12.pX, Code12.pI, Code12.pY, Code12.pI, Code12.pI, Code12.pI, Code12.pY, Code12.pI, Code12.pI, Code12.pY, Code12.pI, Code12.pY]]

def dual : Fin 8 → Pauli 12 :=
  ![![Code12.pX, Code12.pI, Code12.pI, Code12.pI, Code12.pI, Code12.pI, Code12.pI, Code12.pX, Code12.pI, Code12.pI, Code12.pI, Code12.pI],
    ![Code12.pI, Code12.pX, Code12.pI, Code12.pX, Code12.pI, Code12.pI, Code12.pI, Code12.pI, Code12.pI, Code12.pI, Code12.pI, Code12.pI],
    ![Code12.pI, Code12.pI, Code12.pI, Code12.pI, Code12.pX, Code12.pI, Code12.pI, Code12.pI, Code12.pI, Code12.pI, Code12.pI, Code12.pI],
    ![Code12.pI, Code12.pX, Code12.pX, Code12.pI, Code12.pI, Code12.pI, Code12.pI, Code12.pX, Code12.pI, Code12.pI, Code12.pI, Code12.pX],
    ![Code12.pI, Code12.pX, Code12.pI, Code12.pI, Code12.pI, Code12.pI, Code12.pI, Code12.pI, Code12.pI, Code12.pI, Code12.pI, Code12.pI],
    ![Code12.pI, Code12.pX, Code12.pX, Code12.pI, Code12.pI, Code12.pI, Code12.pI, Code12.pX, Code12.pI, Code12.pX, Code12.pI, Code12.pI],
    ![Code12.pX, Code12.pI, Code12.pI, Code12.pI, Code12.pI, Code12.pI, Code12.pI, Code12.pI, Code12.pI, Code12.pI, Code12.pI, Code12.pI],
    ![Code12.pX, Code12.pX, Code12.pX, Code12.pI, Code12.pI, Code12.pI, Code12.pI, Code12.pI, Code12.pI, Code12.pI, Code12.pI, Code12.pI]]

theorem gen_wt : ∀ i, wt (gen i) ≤ 5 := by decide +kernel

theorem gen_symp : ∀ i j, symp (gen i) (gen j) = 0 := by decide +kernel

theorem dual_symp : ∀ k i, symp (dual k) (gen i) = if i = k then 1 else 0 := by decide +kernel

theorem single_check : ∀ j : Fin 12, ∀ p : F × F, p ≠ 0 → ∃ i, locG gen p j i ≠ 0 := by
  decide +kernel

theorem pair_check : ∀ j l : Fin 12, j ≠ l → ∀ p q : F × F, p ≠ 0 → q ≠ 0 →
    ∃ i, locG gen p j i + locG gen q l i ≠ 0 := by
  decide +kernel

end Code12_4

theorem exists_code_12_4 : ∃ g : Fin 8 → Pauli 12, IsCode 12 8 5 g :=
  ⟨Code12_4.gen, isCode_of_checks _ Code12_4.dual Code12_4.dual_symp Code12_4.gen_wt Code12_4.gen_symp
    Code12_4.single_check Code12_4.pair_check⟩

namespace Code12_5

def gen : Fin 7 → Pauli 12 :=
  ![![Code12.pI, Code12.pZ, Code12.pI, Code12.pI, Code12.pZ, Code12.pI, Code12.pI, Code12.pI, Code12.pZ, Code12.pZ, Code12.pZ, Code12.pZ],
    ![Code12.pI, Code12.pI, Code12.pI, Code12.pI, Code12.pI, Code12.pI, Code12.pZ, Code12.pZ, Code12.pX, Code12.pX, Code12.pX, Code12.pX],
    ![Code12.pI, Code12.pI, Code12.pZ, Code12.pZ, Code12.pZ, Code12.pZ, Code12.pX, Code12.pX, Code12.pI, Code12.pI, Code12.pI, Code12.pI],
    ![Code12.pI, Code12.pI, Code12.pX, Code12.pX, Code12.pX, Code12.pX, Code12.pI, Code12.pI, Code12.pI, Code12.pI, Code12.pZ, Code12.pY],
    ![Code12.pI, Code12.pX, Code12.pI, Code12.pY, Code12.pY, Code12.pX, Code12.pX, Code12.pY, Code12.pI, Code12.pI, Code12.pI, Code12.pI],
    ![Code12.pZ, Code12.pZ, Code12.pI, Code12.pI, Code12.pI, Code12.pY, Code12.pI, Code12.pY, Code12.pI, Code12.pX, Code12.pY, Code12.pI],
    ![Code12.pX, Code12.pI, Code12.pZ, Code12.pI, Code12.pX, Code12.pI, Code12.pY, Code12.pI, Code12.pZ, Code12.pI, Code12.pX, Code12.pI]]

def dual : Fin 7 → Pauli 12 :=
  ![![Code12.pX, Code12.pX, Code12.pI, Code12.pI, Code12.pI, Code12.pI, Code12.pI, Code12.pI, Code12.pI, Code12.pI, Code12.pI, Code12.pI],
    ![Code12.pX, Code12.pI, Code12.pX, Code12.pI, Code12.pI, Code12.pX, Code12.pX, Code12.pI, Code12.pI, Code12.pI, Code12.pI, Code12.pI],
    ![Code12.pX, Code12.pI, Code12.pI, Code12.pI, Code12.pI, Code12.pX, Code12.pI, Code12.pI, Code12.pI, Code12.pI, Code12.pI, Code12.pI],
    ![Code12.pI, Code12.pX, Code12.pI, Code12.pI, Code12.pI, Code12.pI, Code12.pI, Code12.pI, Code12.pI, Code12.pI, Code12.pX, Code12.pI],
    ![Code12.pX, Code12.pI, Code12.pI, Code12.pX, Code12.pI, Code12.pX, Code12.pI, Code12.pI, Code12.pI, Code12.pI, Code12.pI, Code12.pI],
    ![Code12.pX, Code12.pI, Code12.pI, Code12.pI, Code12.pI, Code12.pI, Code12.pI, Code12.pI, Code12.pI, Code12.pI, Code12.pI, Code12.pI],
    ![Code12.pX, Code12.pI, Code12.pX, Code12.pI, Code12.pI, Code12.pX, Code12.pI, Code12.pI, Code12.pI, Code12.pI, Code12.pI, Code12.pI]]

theorem gen_wt : ∀ i, wt (gen i) ≤ 6 := by decide +kernel

theorem gen_symp : ∀ i j, symp (gen i) (gen j) = 0 := by decide +kernel

theorem dual_symp : ∀ k i, symp (dual k) (gen i) = if i = k then 1 else 0 := by decide +kernel

theorem single_check : ∀ j : Fin 12, ∀ p : F × F, p ≠ 0 → ∃ i, locG gen p j i ≠ 0 := by
  decide +kernel

theorem pair_check : ∀ j l : Fin 12, j ≠ l → ∀ p q : F × F, p ≠ 0 → q ≠ 0 →
    ∃ i, locG gen p j i + locG gen q l i ≠ 0 := by
  decide +kernel

end Code12_5

theorem exists_code_12_5 : ∃ g : Fin 7 → Pauli 12, IsCode 12 7 6 g :=
  ⟨Code12_5.gen, isCode_of_checks _ Code12_5.dual Code12_5.dual_symp Code12_5.gen_wt Code12_5.gen_symp
    Code12_5.single_check Code12_5.pair_check⟩

namespace Code12_6

def gen : Fin 6 → Pauli 12 :=
  ![![Code12.pI, Code12.pI, Code12.pI, Code12.pI, Code12.pZ, Code12.pZ, Code12.pZ, Code12.pZ, Code12.pZ, Code12.pZ, Code12.pZ, Code12.pZ],
    ![Code12.pZ, Code12.pI, Code12.pI, Code12.pZ, Code12.pI, Code12.pI, Code12.pX, Code12.pX, Code12.pX, Code12.pX, Code12.pX, Code12.pX],
    ![Code12.pI, Code12.pI, Code12.pZ, Code12.pZ, Code12.pX, Code12.pX, Code12.pZ, Code12.pI, Code12.pI, Code12.pI, Code12.pX, Code12.pY],
    ![Code12.pI, Code12.pZ, Code12.pI, Code12.pX, Code12.pY, Code12.pX, Code12.pI, Code12.pY, Code12.pY, Code12.pX, Code12.pI, Code12.pY],
    ![Code12.pI, Code12.pX, Code12.pX, Code12.pI, Code12.pI, Code12.pX, Code12.pX, Code12.pI, Code12.pY, Code12.pX, Code12.pY, Code12.pX],
    ![Code12.pX, Code12.pI, Code12.pY, Code12.pY, Code12.pI, Code12.pI, Code12.pY, Code12.pY, Code12.pZ, Code12.pY, Code12.pI, Code12.pX]]

def dual : Fin 6 → Pauli 12 :=
  ![![Code12.pI, Code12.pX, Code12.pI, Code12.pI, Code12.pX, Code12.pI, Code12.pI, Code12.pI, Code12.pI, Code12.pI, Code12.pI, Code12.pI],
    ![Code12.pX, Code12.pI, Code12.pI, Code12.pI, Code12.pI, Code12.pI, Code12.pI, Code12.pI, Code12.pI, Code12.pI, Code12.pI, Code12.pI],
    ![Code12.pI, Code12.pI, Code12.pX, Code12.pI, Code12.pX, Code12.pI, Code12.pI, Code12.pX, Code12.pI, Code12.pI, Code12.pI, Code12.pI],
    ![Code12.pI, Code12.pX, Code12.pI, Code12.pI, Code12.pI, Code12.pI, Code12.pI, Code12.pI, Code12.pI, Code12.pI, Code12.pI, Code12.pI],
    ![Code12.pI, Code12.pI, Code12.pI, Code12.pI, Code12.pI, Code12.pI, Code12.pI, Code12.pX, Code12.pX, Code12.pI, Code12.pI, Code12.pI],
    ![Code12.pI, Code12.pI, Code12.pI, Code12.pI, Code12.pX, Code12.pI, Code12.pI, Code12.pX, Code12.pI, Code12.pI, Code12.pI, Code12.pI]]

theorem gen_wt : ∀ i, wt (gen i) ≤ 8 := by decide +kernel

theorem gen_symp : ∀ i j, symp (gen i) (gen j) = 0 := by decide +kernel

theorem dual_symp : ∀ k i, symp (dual k) (gen i) = if i = k then 1 else 0 := by decide +kernel

theorem single_check : ∀ j : Fin 12, ∀ p : F × F, p ≠ 0 → ∃ i, locG gen p j i ≠ 0 := by
  decide +kernel

theorem pair_check : ∀ j l : Fin 12, j ≠ l → ∀ p q : F × F, p ≠ 0 → q ≠ 0 →
    ∃ i, locG gen p j i + locG gen q l i ≠ 0 := by
  decide +kernel

end Code12_6

theorem exists_code_12_6 : ∃ g : Fin 6 → Pauli 12, IsCode 12 6 8 g :=
  ⟨Code12_6.gen, isCode_of_checks _ Code12_6.dual Code12_6.dual_symp Code12_6.gen_wt Code12_6.gen_symp
    Code12_6.single_check Code12_6.pair_check⟩

end LowWeight
