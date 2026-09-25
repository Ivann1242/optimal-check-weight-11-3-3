import LowWeight.BitDefs

/-! Bridge lemmas between the algebraic (`Pauli`) and bit-level (`Spec`) descriptions. -/

namespace LowWeight

variable {m n : ℕ}

/-! ### Scalar facts over `F = ZMod 2` -/

theorem F_decide_eq_iff (a b : F) : (decide (a = 1) = decide (b = 1)) ↔ a + b = 0 := by
  revert a b; decide

theorem F_decide_true_iff (a : F) : decide (a = 1) = true ↔ a ≠ 0 := by
  revert a; decide

theorem F_ite_and (a b : F) :
    (if (decide (a = 1) && decide (b = 1)) = true then (1 : F) else 0) = a * b := by
  revert a b; decide

theorem F_ite_symp (a b c d : F) :
    (if ((decide (a = 1) && decide (d = 1)) ^^ (decide (b = 1) && decide (c = 1))) = true
      then (1 : F) else 0) = a * d + b * c := by
  revert a b c d; decide

theorem F_or_ne (p : F × F) : (decide (p.1 = 1) || decide (p.2 = 1)) = decide (p ≠ 0) := by
  obtain ⟨a, b⟩ := p; revert a b; decide

/-- The parity map `F → BitVec 1`. -/
def parity : F →+ BitVec 1 where
  toFun a := if a = 1 then 1 else 0
  map_zero' := by decide
  map_add' := by decide

theorem parity_ite (P : Prop) [Decidable P] :
    parity (if P then (1 : F) else 0) = if P then (1 : BitVec 1) else 0 := by
  split_ifs <;> decide

/-- A 1-bit counter sum is the parity of the corresponding `F`-sum. -/
theorem bv1_sum {ι : Type*} (s : Finset ι) (P : ι → Prop) [DecidablePred P] :
    (∑ j ∈ s, if P j then (1 : BitVec 1) else 0) =
      parity (∑ j ∈ s, if P j then (1 : F) else 0) := by
  rw [map_sum]; simp only [parity_ite]

/-! ### Symplectic form against single-qubit operators -/

theorem symp_single (j : Fin n) (p : F × F) (v : Pauli n) :
    symp (Pi.single j p) v = p.1 * (v j).2 + p.2 * (v j).1 := by
  unfold symp
  rw [Finset.sum_eq_single j]
  · simp
  · intro b _ hb; simp [hb]
  · simp

theorem pauliOf_ne_zero (t : Fin 3) : pauliOf t ≠ 0 := by
  fin_cases t <;> decide

theorem pauliOf_add_ne_zero {t s : Fin 3} (h : t ≠ s) : pauliOf t + pauliOf s ≠ 0 := by
  fin_cases t <;> fin_cases s <;> first | exact absurd rfl h | decide

/-! ### B1, B2: syndromes -/

theorem synP_apply (g : Fin m → Pauli n) (j : Fin n) (t : Fin 3) (i : Fin m) :
    synP g j t i = decide (symp (err j t) (g i) = 1) := by
  rw [err, symp_single]
  unfold synP syn toX toZ
  generalize g i j = p
  obtain ⟨a, b⟩ := p
  fin_cases t <;> revert a b <;> decide

theorem synP_eq_iff (g : Fin m → Pauli n) (j l : Fin n) (t s : Fin 3) :
    synP g j t = synP g l s ↔ ∀ i, symp (err j t + err l s) (g i) = 0 := by
  constructor
  · intro h i
    have := congrFun h i
    rw [synP_apply, synP_apply, F_decide_eq_iff] at this
    rwa [symp_add_left]
  · intro h; funext i
    rw [synP_apply, synP_apply, F_decide_eq_iff, ← symp_add_left]; exact h i

theorem synP_ne_zero_iff (g : Fin m → Pauli n) (j : Fin n) (t : Fin 3) :
    (∃ i, synP g j t i = true) ↔ ∃ i, symp (err j t) (g i) ≠ 0 := by
  simp only [synP_apply, F_decide_true_iff]

/-! ### B3: weights of errors -/

theorem wt_single (j : Fin n) {p : F × F} (hp : p ≠ 0) : wt (Pi.single j p : Pauli n) = 1 := by
  unfold wt
  rw [Finset.card_eq_one]; refine ⟨j, ?_⟩
  ext q; by_cases hq : q = j
  · subst hq; simp [hp]
  · simp [Pi.single_apply, hq]

theorem wt_err (j : Fin n) (t : Fin 3) : wt (err j t) = 1 :=
  wt_single j (pauliOf_ne_zero t)

theorem err_ne_zero (j : Fin n) (t : Fin 3) : err j t ≠ 0 := by
  intro h; have := wt_err j t; rw [h, wt_zero] at this; exact absurd this (by decide)

theorem wt_err_add_err {j l : Fin n} (hjl : j ≠ l) (t s : Fin 3) :
    wt (err j t + err l s) = 2 := by
  unfold wt
  rw [Finset.card_eq_two]; refine ⟨j, l, hjl, ?_⟩
  ext q
  have ht := pauliOf_ne_zero t
  have hs := pauliOf_ne_zero s
  by_cases hqj : q = j
  · subst hqj; simp [err, Pi.single_apply, hjl, ht]
  · by_cases hql : q = l
    · subst hql; simp [err, Pi.single_apply, Ne.symm hjl, hs]
    · simp [err, Pi.single_apply, hqj, hql]

theorem err_add_err_same (j : Fin n) (t s : Fin 3) :
    err j t + err j s = Pi.single j (pauliOf t + pauliOf s) := by
  rw [err, err, Pi.single_add]

theorem wt_err_add_err_same (j : Fin n) {t s : Fin 3} (hts : t ≠ s) :
    wt (err j t + err j s) = 1 := by
  rw [err_add_err_same]; exact wt_single j (pauliOf_add_ne_zero hts)

/-! ### B7: supports -/

theorem toX_or_toZ (g : Fin m → Pauli n) (i : Fin m) (j : Fin n) :
    (toX g i j || toZ g i j) = decide (g i j ≠ 0) := F_or_ne (g i j)

theorem suppIs_of (g : Fin m → Pauli n) (i : Fin m) (S : Finset (Fin n))
    (h : ∀ j, g i j ≠ 0 ↔ j ∈ S) : SuppIs (toX g) (toZ g) i S := by
  intro j; rw [toX_or_toZ]; exact decide_eq_decide.mpr (h j)

/-! ### B4: row weights -/

theorem rowWt_eq (g : Fin m → Pauli n) (i : Fin m) :
    rowWt (toX g) (toZ g) i = BitVec.ofNat 4 (wt (g i)) := by
  unfold rowWt wt
  simp only [toX_or_toZ, decide_eq_true_eq]
  rw [Finset.sum_boole]
  rfl

theorem rowWt_le (g : Fin m → Pauli n) (i : Fin m) {k : ℕ} (h : wt (g i) ≤ k) (hk : k ≤ 15) :
    rowWt (toX g) (toZ g) i ≤ BitVec.ofNat 4 k := by
  rw [rowWt_eq, BitVec.le_def, BitVec.toNat_ofNat, BitVec.toNat_ofNat]
  rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
  exact h

/-! ### B5: commutation -/

theorem rowSymp_eq (g : Fin m → Pauli n) (i₁ i₂ : Fin m) :
    rowSymp (toX g) (toZ g) i₁ i₂ = parity (symp (g i₁) (g i₂)) := by
  unfold rowSymp
  rw [bv1_sum]; congr 1
  unfold symp; refine Finset.sum_congr rfl fun j _ => ?_
  exact F_ite_symp _ _ _ _

theorem rowSymp_eq_zero (g : Fin m → Pauli n) {i₁ i₂ : Fin m} (h : symp (g i₁) (g i₂) = 0) :
    rowSymp (toX g) (toZ g) i₁ i₂ = 0 := by
  rw [rowSymp_eq, h, map_zero]

/-! ### B6: span equations -/

theorem spanEq_of (g : Fin m → Pauli n) (c : Fin m → F) {j l : Fin n} (hjl : j ≠ l)
    (t s : Fin 3) (hv : ∑ i, c i • g i = err j t + err l s) :
    SpanEq (toX g) (toZ g) (fun i => decide (c i = 1)) j l t s := by
  intro q
  have hq := congrFun hv q
  rw [Finset.sum_apply] at hq
  have h1 := congrArg Prod.fst hq
  have h2 := congrArg Prod.snd hq
  rw [Prod.fst_sum] at h1
  rw [Prod.snd_sum] at h2
  simp only [Pi.smul_apply, Prod.smul_fst, Prod.smul_snd, smul_eq_mul, Pi.add_apply, Prod.fst_add,
    Prod.snd_add] at h1 h2
  constructor
  · rw [bv1_sum]; unfold toX
    simp only [F_ite_and]; rw [h1]
    by_cases hqj : q = j
    · subst hqj
      have hlq : ¬ q = l := hjl
      simp only [err, Pi.single_apply, hlq, ite_true, ite_false, decide_true, decide_false,
        Bool.true_and, Bool.false_and, Bool.or_false, Prod.fst_zero, add_zero]
      fin_cases t <;> decide
    · by_cases hql : q = l
      · subst hql
        simp only [err, Pi.single_apply, hqj, ite_true, ite_false, decide_true, decide_false,
          Bool.true_and, Bool.false_and, Bool.false_or, Prod.fst_zero, zero_add]
        fin_cases s <;> decide
      · simp only [err, Pi.single_apply, hqj, hql, ite_false, decide_false,
          Bool.false_and, Bool.false_or, Prod.fst_zero, add_zero]
        decide
  · rw [bv1_sum]; unfold toZ
    simp only [F_ite_and]; rw [h2]
    by_cases hqj : q = j
    · subst hqj
      have hlq : ¬ q = l := hjl
      simp only [err, Pi.single_apply, hlq, ite_true, ite_false, decide_true, decide_false,
        Bool.true_and, Bool.false_and, Bool.or_false, Prod.snd_zero, add_zero]
      fin_cases t <;> decide
    · by_cases hql : q = l
      · subst hql
        simp only [err, Pi.single_apply, hqj, ite_true, ite_false, decide_true, decide_false,
          Bool.true_and, Bool.false_and, Bool.false_or, Prod.snd_zero, zero_add]
        fin_cases s <;> decide
      · simp only [err, Pi.single_apply, hqj, hql, ite_false, decide_false,
          Bool.false_and, Bool.false_or, Prod.snd_zero, add_zero]
        decide

end LowWeight
