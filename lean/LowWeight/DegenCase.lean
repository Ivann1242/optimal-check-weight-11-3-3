import LowWeight.Transport
import LowWeight.Exchange

/-! The degenerate case: a code of distance `≥ 3` without weight-one elements in its stabilizer
group, but with a weight-two element, can be normalized to one of the `DegenLayoutSpec` /
`DegenGenSpec` forms. -/

namespace LowWeight

variable {m n : ℕ}

/-! ### Invariants -/

/-- No element of the span has weight 1. -/
def DNoWt1 (g : Fin m → Pauli n) : Prop :=
  ∀ v ∈ Submodule.span F (Set.range g), wt v ≠ 1

/-- Every weight-two element of the span is a combination of the first `r` generators. -/
def DWProp (r : ℕ) (g : Fin m → Pauli n) : Prop :=
  ∀ v ∈ Submodule.span F (Set.range g), wt v = 2 →
    ∃ c : Fin m → F, (∀ i : Fin m, r ≤ i.val → c i = 0) ∧ ∑ i, c i • g i = v

theorem DNoWt1.map {g : Fin m → Pauli n} (T : Pauli n ≃ₗ[F] Pauli n)
    (hwt : ∀ v, wt (T v) = wt v) (h : DNoWt1 g) : DNoWt1 (fun i => T (g i)) := by
  intro v hv
  rw [mem_span_map_iff] at hv
  have hw : wt (T.symm v) = wt v := by rw [← hwt, T.apply_symm_apply]
  rw [← hw]; exact h _ hv

theorem DWProp.map {r : ℕ} {g : Fin m → Pauli n} (T : Pauli n ≃ₗ[F] Pauli n)
    (hwt : ∀ v, wt (T v) = wt v) (h : DWProp r g) : DWProp r (fun i => T (g i)) := by
  intro v hv h2
  rw [mem_span_map_iff] at hv
  have hw : wt (T.symm v) = wt v := by rw [← hwt, T.apply_symm_apply]
  obtain ⟨c, hc0, hc⟩ := h _ hv (hw.trans h2)
  refine ⟨c, hc0, ?_⟩
  have := congrArg T hc
  rw [T.apply_symm_apply, map_sum] at this
  simp only [map_smul] at this
  exact this

theorem dperm {f : Fin m → Pauli n} (hf : IsCode n m 4 f) (hl : DNoWt1 f) {r : ℕ}
    (hW : DWProp r f) (σ : Equiv.Perm (Fin n)) :
    IsCode n m 4 (fun i => permP σ (f i)) ∧ DNoWt1 (fun i => permP σ (f i)) ∧
      DWProp r (fun i => permP σ (f i)) :=
  ⟨hf.perm σ, hl.map _ (wt_permP σ), hW.map _ (wt_permP σ)⟩

/-! ### Syndrome facts -/

theorem dsyn_nz {f : Fin m → Pauli n} (hf : IsCode n m 4 f) (hl : DNoWt1 f)
    (j : Fin n) (t : Fin 3) : ∃ i, synP f j t i = true := by
  rw [synP_ne_zero_iff]
  by_contra hc
  push Not at hc
  have hw := wt_err j t
  exact hl _ (hf.2.2.2 _ (by omega) (by omega) hc) hw

theorem dsyn_ne_same {f : Fin m → Pauli n} (hf : IsCode n m 4 f) (hl : DNoWt1 f)
    (j : Fin n) {t s : Fin 3} (hts : t ≠ s) : synP f j t ≠ synP f j s := by
  intro he
  rw [synP_eq_iff] at he
  have hw := wt_err_add_err_same j hts
  exact hl _ (hf.2.2.2 _ (by omega) (by omega) he) hw

theorem dcoll {f : Fin m → Pauli n} (hf : IsCode n m 4 f) {r : ℕ} (hW : DWProp r f)
    {j l : Fin n} (hjl : j ≠ l) (t s : Fin 3) (he : synP f j t = synP f l s) :
    ∃ c : Fin m → F, (∀ i : Fin m, r ≤ i.val → c i = 0) ∧
      ∑ i, c i • f i = err j t + err l s := by
  rw [synP_eq_iff] at he
  have hw := wt_err_add_err hjl t s
  exact hW _ (hf.2.2.2 _ (by omega) (by omega) he) hw

open Classical in
/-- Coefficients explaining a syndrome collision (if one exists). -/
noncomputable def collC (r : ℕ) (f : Fin m → Pauli n) :
    Fin n → Fin n → Fin 3 → Fin 3 → Fin m → Bool :=
  fun j l t s =>
    if h : ∃ c : Fin m → F, (∀ i : Fin m, r ≤ i.val → c i = 0) ∧
        ∑ i, c i • f i = err j t + err l s
    then fun i => decide (h.choose i = 1) else fun _ => false

theorem collC_clause {f : Fin m → Pauli n} (hf : IsCode n m 4 f) {r : ℕ} (hW : DWProp r f)
    {j l : Fin n} (hjl : j ≠ l) (t s : Fin 3) :
    (∃ i, syn (toX f) (toZ f) j t i ≠ syn (toX f) (toZ f) l s i) ∨
      ((∀ i : Fin m, r ≤ i.val → collC r f j l t s i = false) ∧
        SpanEq (toX f) (toZ f) (collC r f j l t s) j l t s) := by
  by_cases he : synP f j t = synP f l s
  · right
    have h := dcoll hf hW hjl t s he
    have hc : collC r f j l t s = fun i => decide (h.choose i = 1) := by
      unfold collC
      split
      · rfl
      · contradiction
    rw [hc]
    refine ⟨fun i hi => ?_, spanEq_of f _ hjl t s h.choose_spec.2⟩
    show decide (h.choose i = 1) = false
    rw [h.choose_spec.1 i hi]; decide
  · left
    exact Function.ne_iff.mp he

theorem dnocoll {f : Fin m → Pauli n} (hf : IsCode n m 4 f) {r : ℕ} (hW : DWProp r f) {tt : ℕ}
    (hv : ∀ i : Fin m, i.val < r → ∀ j : Fin n, tt ≤ j.val → f i j = 0)
    {j l : Fin n} (hjl : j ≠ l) (hl : tt ≤ l.val) (t s : Fin 3) :
    ∃ i, syn (toX f) (toZ f) j t i ≠ syn (toX f) (toZ f) l s i := by
  by_contra hcon
  push Not at hcon
  have he : synP f j t = synP f l s := funext hcon
  obtain ⟨c, hc0, hc⟩ := dcoll hf hW hjl t s he
  have h1 := congrFun hc l
  rw [Finset.sum_apply] at h1
  have hz : ∑ i, (c i • f i) l = 0 := Finset.sum_eq_zero fun i _ => by
    by_cases hi : r ≤ i.val
    · simp [hc0 i hi]
    · simp [hv i (by omega) l hl]
  rw [hz] at h1
  have hlj : l ≠ j := Ne.symm hjl
  have h2 : (err j t + err l s) l = pauliOf s := by
    simp [err, hlj]
  rw [h2] at h1
  exact pauliOf_ne_zero s h1.symm

theorem dcommon {f : Fin m → Pauli n} (hf : IsCode n m 4 f) (hl : DNoWt1 f)
    (hLC : ∀ j, colLt (synP f j 0) (synP f j 1) ∧ colLt (synP f j 1) (synP f j 2)) :
    CommonSpec 4 (toX f) (toZ f) :=
  ⟨fun i => rowWt_le f i (hf.2.1 i) (by norm_num),
    fun i₁ i₂ => rowSymp_eq_zero f (hf.2.2.1 i₁ i₂), fun j t => dsyn_nz hf hl j t, hLC⟩

/-! ### Normalization -/

theorem dnormalize {f : Fin m → Pauli n} (hf : IsCode n m 4 f) (hl : DNoWt1 f) {r : ℕ}
    (hW : DWProp r f) (tt : ℕ) :
    ∃ f' : Fin m → Pauli n, IsCode n m 4 f' ∧ DNoWt1 f' ∧ DWProp r f' ∧
      (∀ j, colLt (synP f' j 0) (synP f' j 1) ∧ colLt (synP f' j 1) (synP f' j 2)) ∧
      (∀ j l : Fin n, tt ≤ j.val → j.val + 1 = l.val → colLe (synP f' j 0) (synP f' l 0)) ∧
      (∀ i, wt (f' i) = wt (f i)) ∧
      (∀ i (j : Fin n), j.val < tt → (f' i j ≠ 0 ↔ f i j ≠ 0)) ∧
      (∀ i, (∀ j : Fin n, tt ≤ j.val → f i j = 0) → ∀ j : Fin n, tt ≤ j.val → f' i j = 0) := by
  obtain ⟨M, hM⟩ := exists_localCanon f fun j =>
    ⟨dsyn_ne_same hf hl j (by decide), dsyn_ne_same hf hl j (by decide),
      dsyn_ne_same hf hl j (by decide)⟩
  have hg1c : IsCode n m 4 (fun i => localP M (f i)) := hf.localMap M
  have hl1 : DNoWt1 (fun i => localP M (f i)) := hl.map (localP M) (wt_localP M)
  have hW1 : DWProp r (fun i => localP M (f i)) := hW.map (localP M) (wt_localP M)
  obtain ⟨τ, hτfix, hτ⟩ := exists_sort_tail (fun i => localP M (f i)) tt
  refine ⟨fun i => permP τ (localP M (f i)), hg1c.perm τ, hl1.map (permP τ) (wt_permP τ),
    hW1.map (permP τ) (wt_permP τ), fun j => ?_, hτ, fun i => ?_, fun i j hj => ?_,
    fun i hi j hj => ?_⟩
  · rw [synP_permP, synP_permP, synP_permP]; exact hM (τ j)
  · rw [wt_permP, wt_localP]
  · simp only [permP_apply, hτfix j hj, localP_apply]
    exact (M j).map_ne_zero_iff
  · have hτj : tt ≤ (τ j).val := by
      by_contra hlt
      push Not at hlt
      have h1 := τ.injective (hτfix (τ j) hlt)
      rw [h1] at hlt
      omega
    simp only [permP_apply, localP_apply, hi (τ j) hτj, map_zero]

/-! ### Final spec lemmas -/

theorem dlayout {r tt : ℕ} {S : Fin m → Finset (Fin n)} {f : Fin m → Pauli n}
    (hf : IsCode n m 4 f) (hl : DNoWt1 f) (hW : DWProp r f)
    (hS : ∀ i : Fin m, i.val < r → ∀ j, f i j ≠ 0 ↔ j ∈ S i)
    (hStt : ∀ i : Fin m, i.val < r → ∀ j ∈ S i, j.val < tt) :
    ∃ (g' : Fin m → Pauli n) (c : Fin n → Fin n → Fin 3 → Fin 3 → Fin m → Bool),
      DegenLayoutSpec 4 r tt S (toX g') (toZ g') c := by
  obtain ⟨f', hf', hl', hW', hLC, hsort, -, hsupp, hvan⟩ := dnormalize hf hl hW tt
  have hv0 : ∀ i : Fin m, i.val < r → ∀ j : Fin n, tt ≤ j.val → f i j = 0 := by
    intro i hi j hj
    by_contra hne
    have := hStt i hi j ((hS i hi j).mp hne)
    omega
  have hv' : ∀ i : Fin m, i.val < r → ∀ j : Fin n, tt ≤ j.val → f' i j = 0 :=
    fun i hi => hvan i (hv0 i hi)
  refine ⟨f', collC r f', dcommon hf' hl' hLC, fun i hi => suppIs_of f' i (S i) fun j => ?_,
    ?_, ?_, ?_⟩
  · by_cases hj : j.val < tt
    · rw [hsupp i j hj]; exact hS i hi j
    · push Not at hj
      rw [hv' i hi j hj]
      simp only [ne_eq, not_true_eq_false, false_iff]
      intro hmem; have := hStt i hi j hmem; omega
  · intro j l hjl hlt t s
    exact dnocoll hf' hW' hv' (ne_of_lt hjl) hlt t s
  · intro j l hjl _ t s
    exact collC_clause hf' hW' (ne_of_lt hjl) t s
  · intro j l hj hjl
    have hne : synP f' j 0 ≠ synP f' l 0 := by
      intro he
      obtain ⟨i, hi⟩ := dnocoll hf' hW' hv' (j := j) (l := l)
        (fun h => by rw [h] at hjl; omega) (by omega) 0 0
      exact hi (congrFun he i)
    exact colLt_of_colLe_of_ne (hsort j l hj hjl) hne

theorem dgeneral {r : ℕ} {f : Fin m → Pauli n} (hf : IsCode n m 4 f) (hl : DNoWt1 f)
    (hW : DWProp r f)
    (h0 : ∀ i : Fin m, i.val = 0 → ∀ j : Fin n, f i j ≠ 0 ↔ j.val < 2)
    (hw2 : ∀ i : Fin m, i.val < r → wt (f i) ≤ 2) :
    ∃ (g' : Fin m → Pauli n) (c : Fin n → Fin n → Fin 3 → Fin 3 → Fin m → Bool),
      DegenGenSpec 4 r (toX g') (toZ g') c := by
  obtain ⟨f', hf', hl', hW', hLC, hsort, hwt, hsupp, hvan⟩ := dnormalize hf hl hW 2
  refine ⟨f', collC r f', dcommon hf' hl' hLC, fun i hi j => ?_,
    fun i hi => rowWt_le f' i (by rw [hwt]; exact hw2 i hi) (by norm_num),
    fun j l hjl t s => collC_clause hf' hW' (ne_of_lt hjl) t s, hsort⟩
  rw [toX_or_toZ]
  by_cases hj : j.val < 2
  · rw [decide_eq_decide]; exact (hsupp i j hj).trans (h0 i hi j)
  · have : f' i j = 0 := hvan i (fun j' hj' => by
      by_contra hne; have := (h0 i hi j').mp hne; omega) j (by omega)
    simp [this, hj]

/-! ### Preparation: exchange in a basis of the weight-two span -/

theorem dprep {g : Fin m → Pauli n} (hg : IsCode n m 4 g)
    (h2 : ∃ v ∈ Submodule.span F (Set.range g), wt v = 2) :
    ∃ r, 1 ≤ r ∧ r ≤ m ∧ ∃ g1 : Fin m → Pauli n, IsCode n m 4 g1 ∧ DWProp r g1 ∧
      (∀ i : Fin m, i.val < r → wt (g1 i) = 2) ∧
      Submodule.span F (Set.range g1) = Submodule.span F (Set.range g) := by
  classical
  let D : Set (Pauli n) := {v | v ∈ Submodule.span F (Set.range g) ∧ wt v = 2}
  obtain ⟨B, hBD, hBspan0, hBli0⟩ :=
    @exists_linearIndependent F (Pauli n) _ _ (inferInstance : Module F (Pauli n)) D
  have hBspan : Submodule.span F B = Submodule.span F D := hBspan0
  have hBli : LinearIndependent F (Subtype.val : B → Pauli n) := hBli0
  have : Fintype B := Fintype.ofFinite B
  let e : Fin (Fintype.card B) ≃ B := (Fintype.equivFin B).symm
  let b : Fin (Fintype.card B) → Pauli n := fun i => (e i).1
  have hbli : LinearIndependent F b := hBli.comp e e.injective
  have hbD : ∀ i, b i ∈ D := fun i => hBD (e i).2
  obtain ⟨hr, g1, hg1, hg1b, hspan⟩ :=
    hg.exchange b hbli (fun i => (hbD i).1) (fun i => by rw [(hbD i).2]; norm_num)
  have hrange : Set.range b = B := by
    ext x; constructor
    · rintro ⟨i, rfl⟩; exact (e i).2
    · intro hx; exact ⟨e.symm ⟨x, hx⟩, by simp [b]⟩
  have hvW : ∀ v ∈ Submodule.span F (Set.range g), wt v = 2 →
      v ∈ Submodule.span F (Set.range b) := by
    intro v hv hw
    rw [hrange, hBspan]; exact Submodule.subset_span ⟨hv, hw⟩
  obtain ⟨v, hvS, hv2⟩ := h2
  have hr1 : 1 ≤ Fintype.card B := by
    by_contra h0
    have hr0 : Fintype.card B = 0 := by omega
    have hBe : B = ∅ := Set.isEmpty_coe_sort.mp (Fintype.card_eq_zero_iff.mp hr0)
    have hvB : v ∈ Submodule.span F B := by
      rw [hBspan]; exact Submodule.subset_span ⟨hvS, hv2⟩
    rw [hBe, Submodule.span_empty, Submodule.mem_bot] at hvB
    rw [hvB, wt_zero] at hv2
    omega
  refine ⟨Fintype.card B, hr1, hr, g1, hg1, ?_, ?_, hspan⟩
  · intro w hw hw2
    rw [hspan] at hw
    obtain ⟨c', hc'⟩ := (Submodule.mem_span_range_iff_exists_fun F).mp (hvW w hw hw2)
    refine ⟨fun i => if h : i.val < Fintype.card B then c' ⟨i.val, h⟩ else 0,
      fun i hi => by simp only [show ¬ i.val < Fintype.card B by omega, ↓reduceDIte], ?_⟩
    rw [← hc']
    symm
    apply Fintype.sum_of_injective (Fin.castLE hr) (Fin.castLE_injective hr)
    · intro i hi
      have : ¬ i.val < Fintype.card B := fun h => hi ⟨⟨i.val, h⟩, Fin.ext rfl⟩
      simp only [this, ↓reduceDIte, zero_smul]
    · intro i
      rw [hg1b i]
      simp only [Fin.val_castLE, Fin.is_lt, ↓reduceDIte]
  · intro i hi
    have := hg1b ⟨i.val, hi⟩
    have hci : Fin.castLE hr ⟨i.val, hi⟩ = i := Fin.ext rfl
    rw [hci] at this
    rw [this]; exact (hbD _).2

/-! ### Supports and permutations -/

theorem wt2_supp {v : Pauli n} (h : wt v = 2) :
    ∃ p q : Fin n, p ≠ q ∧ ∀ j, v j ≠ 0 ↔ j = p ∨ j = q := by
  classical
  unfold wt at h
  obtain ⟨p, q, hpq, hs⟩ := Finset.card_eq_two.mp h
  refine ⟨p, q, hpq, fun j => ?_⟩
  have hj : j ∈ Finset.univ.filter (fun j => v j ≠ 0) ↔ j ∈ ({p, q} : Finset (Fin n)) := by
    rw [hs]
  simpa using hj

theorem exists_perm_prefix {k : ℕ} (a : Fin k → Fin n) (ha : Function.Injective a) :
    ∃ σ : Equiv.Perm (Fin n), ∀ (j : Fin n) (i : Fin k), j.val = i.val → σ j = a i := by
  classical
  have hk : k ≤ n := by simpa using Fintype.card_le_of_injective a ha
  let e1 : {x : Fin n // x.val < k} ≃ Fin k :=
    { toFun := fun x => ⟨x.1.val, x.2⟩
      invFun := fun i => ⟨⟨i.val, by omega⟩, i.2⟩
      left_inv := fun x => rfl
      right_inv := fun i => rfl }
  let e : {x : Fin n // x.val < k} ≃ {y : Fin n // y ∈ Set.range a} :=
    e1.trans (Equiv.ofInjective a ha)
  refine ⟨e.extendSubtype, fun j i hji => ?_⟩
  have hj : j.val < k := by have := i.2; omega
  rw [Equiv.extendSubtype_apply_of_mem e j hj]
  show a (e1 ⟨j, hj⟩) = a i
  congr 1; exact Fin.ext hji

theorem permP_supp2 (σ : Equiv.Perm (Fin n)) {v : Pauli n} {p q : Fin n}
    (hv : ∀ j, v j ≠ 0 ↔ j = p ∨ j = q) (a b : Fin n) (ha : σ a = p) (hb : σ b = q) :
    ∀ j, permP σ v j ≠ 0 ↔ j ∈ ({a, b} : Finset (Fin n)) := by
  intro j
  rw [permP_apply, hv, ← ha, ← hb, σ.injective.eq_iff, σ.injective.eq_iff]
  simp

theorem mem_pair_val {a b j : Fin n} :
    j ∈ ({a, b} : Finset (Fin n)) ↔ j.val = a.val ∨ j.val = b.val := by
  simp [Fin.ext_iff]

theorem dvals [NeZero n] (hn : 4 ≤ n) :
    (0 : Fin n).val = 0 ∧ (1 : Fin n).val = 1 ∧ (2 : Fin n).val = 2 ∧ (3 : Fin n).val = 3 := by
  refine ⟨rfl, ?_, ?_, ?_⟩ <;> simp <;> exact Nat.mod_eq_of_lt (by omega)

/-! ### The four shapes -/

theorem dpair [NeZero n] (hn : 4 ≤ n) {r : ℕ} {f : Fin m → Pauli n} (hf : IsCode n m 4 f)
    (hl : DNoWt1 f) (hW : DWProp r f) {x y : Fin n} (hxy : x ≠ y)
    (hs : ∀ i : Fin m, i.val < r → ∀ j, f i j ≠ 0 ↔ j = x ∨ j = y) :
    ∃ (g' : Fin m → Pauli n) (c : Fin n → Fin n → Fin 3 → Fin 3 → Fin m → Bool),
      DegenLayoutSpec 4 r 2 (fun _ => ({0, 1} : Finset (Fin n))) (toX g') (toZ g') c := by
  obtain ⟨v0, v1, -, -⟩ := dvals hn
  obtain ⟨σ, hσ⟩ := exists_perm_prefix ![x, y] (by
    intro i j h; fin_cases i <;> fin_cases j <;> simp_all)
  have s0 : σ 0 = x := by simpa using hσ 0 0 (by rw [v0]; rfl)
  have s1 : σ 1 = y := by simpa using hσ 1 1 (by rw [v1]; rfl)
  obtain ⟨hf', hl', hW'⟩ := dperm hf hl hW σ
  refine dlayout hf' hl' hW' (fun i hi => permP_supp2 σ (hs i hi) 0 1 s0 s1) ?_
  intro i _ j hj
  rw [mem_pair_val, v0, v1] at hj; omega

theorem dchain [NeZero n] (hn : 4 ≤ n) {f : Fin m → Pauli n} (hf : IsCode n m 4 f)
    (hl : DNoWt1 f) (hW : DWProp 2 f) {x y z : Fin n} (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z)
    (h0 : ∀ i : Fin m, i.val = 0 → ∀ j, f i j ≠ 0 ↔ j = x ∨ j = y)
    (h1 : ∀ i : Fin m, i.val = 1 → ∀ j, f i j ≠ 0 ↔ j = y ∨ j = z) :
    ∃ (g' : Fin m → Pauli n) (c : Fin n → Fin n → Fin 3 → Fin 3 → Fin m → Bool),
      DegenLayoutSpec 4 2 3 (fun i => if i.val = 0 then ({0, 1} : Finset (Fin n)) else {1, 2})
        (toX g') (toZ g') c := by
  obtain ⟨v0, v1, v2, -⟩ := dvals hn
  obtain ⟨σ, hσ⟩ := exists_perm_prefix ![x, y, z] (by
    intro i j h; fin_cases i <;> fin_cases j <;> simp_all)
  have s0 : σ 0 = x := by simpa using hσ 0 0 (by rw [v0]; rfl)
  have s1 : σ 1 = y := by simpa using hσ 1 1 (by rw [v1]; rfl)
  have s2 : σ 2 = z := by simpa using hσ 2 2 (by rw [v2]; rfl)
  obtain ⟨hf', hl', hW'⟩ := dperm hf hl hW σ
  refine dlayout hf' hl' hW' (fun i hi => ?_) ?_
  · by_cases hi0 : i.val = 0
    · simp only [hi0, ite_true]; exact permP_supp2 σ (h0 i hi0) 0 1 s0 s1
    · simp only [hi0, ite_false]; exact permP_supp2 σ (h1 i (by omega)) 1 2 s1 s2
  · intro i _ j hj
    by_cases hi0 : i.val = 0
    · simp only [hi0, ite_true] at hj; rw [mem_pair_val, v0, v1] at hj; omega
    · simp only [hi0, ite_false] at hj; rw [mem_pair_val, v1, v2] at hj; omega

theorem ddisj [NeZero n] (hn : 4 ≤ n) {f : Fin m → Pauli n} (hf : IsCode n m 4 f)
    (hl : DNoWt1 f) (hW : DWProp 2 f) {x y z w : Fin n} (hxy : x ≠ y) (hxz : x ≠ z)
    (hxw : x ≠ w) (hyz : y ≠ z) (hyw : y ≠ w) (hzw : z ≠ w)
    (h0 : ∀ i : Fin m, i.val = 0 → ∀ j, f i j ≠ 0 ↔ j = x ∨ j = y)
    (h1 : ∀ i : Fin m, i.val = 1 → ∀ j, f i j ≠ 0 ↔ j = z ∨ j = w) :
    ∃ (g' : Fin m → Pauli n) (c : Fin n → Fin n → Fin 3 → Fin 3 → Fin m → Bool),
      DegenLayoutSpec 4 2 4 (fun i => if i.val = 0 then ({0, 1} : Finset (Fin n)) else {2, 3})
        (toX g') (toZ g') c := by
  obtain ⟨v0, v1, v2, v3⟩ := dvals hn
  obtain ⟨σ, hσ⟩ := exists_perm_prefix ![x, y, z, w] (by
    intro i j h; fin_cases i <;> fin_cases j <;> simp_all)
  have s0 : σ 0 = x := by simpa using hσ 0 0 (by rw [v0]; rfl)
  have s1 : σ 1 = y := by simpa using hσ 1 1 (by rw [v1]; rfl)
  have s2 : σ 2 = z := by simpa using hσ 2 2 (by rw [v2]; rfl)
  have s3 : σ 3 = w := by simpa using hσ 3 3 (by rw [v3]; rfl)
  obtain ⟨hf', hl', hW'⟩ := dperm hf hl hW σ
  refine dlayout hf' hl' hW' (fun i hi => ?_) ?_
  · by_cases hi0 : i.val = 0
    · simp only [hi0, ite_true]; exact permP_supp2 σ (h0 i hi0) 0 1 s0 s1
    · simp only [hi0, ite_false]; exact permP_supp2 σ (h1 i (by omega)) 2 3 s2 s3
  · intro i _ j hj
    by_cases hi0 : i.val = 0
    · simp only [hi0, ite_true] at hj; rw [mem_pair_val, v0, v1] at hj; omega
    · simp only [hi0, ite_false] at hj; rw [mem_pair_val, v2, v3] at hj; omega

theorem dgen [NeZero n] (hn : 4 ≤ n) {r : ℕ} {f : Fin m → Pauli n} (hf : IsCode n m 4 f)
    (hl : DNoWt1 f) (hW : DWProp r f) {x y : Fin n} (hxy : x ≠ y)
    (h0 : ∀ i : Fin m, i.val = 0 → ∀ j, f i j ≠ 0 ↔ j = x ∨ j = y)
    (hw : ∀ i : Fin m, i.val < r → wt (f i) = 2) :
    ∃ (g' : Fin m → Pauli n) (c : Fin n → Fin n → Fin 3 → Fin 3 → Fin m → Bool),
      DegenGenSpec 4 r (toX g') (toZ g') c := by
  obtain ⟨v0, v1, -, -⟩ := dvals hn
  obtain ⟨σ, hσ⟩ := exists_perm_prefix ![x, y] (by
    intro i j h; fin_cases i <;> fin_cases j <;> simp_all)
  have s0 : σ 0 = x := by simpa using hσ 0 0 (by rw [v0]; rfl)
  have s1 : σ 1 = y := by simpa using hσ 1 1 (by rw [v1]; rfl)
  obtain ⟨hf', hl', hW'⟩ := dperm hf hl hW σ
  refine dgeneral hf' hl' hW' (fun i hi j => ?_) (fun i hi => by rw [wt_permP, hw i hi])
  rw [permP_supp2 σ (h0 i hi) 0 1 s0 s1 j, mem_pair_val, v0, v1]
  omega

/-! ### Main theorem -/

/-- Main result of the degenerate case (the binders of `g'` and `c` carry type ascriptions so
that the `Finset` literals elaborate in `Finset (Fin n)`). -/
theorem degen_spec {n m : ℕ} [NeZero n] (hn : 4 ≤ n) {g : Fin m → Pauli n} (hg : IsCode n m 4 g)
    (h1 : ∀ v ∈ Submodule.span F (Set.range g), wt v ≠ 1)
    (h2 : ∃ v ∈ Submodule.span F (Set.range g), wt v = 2) :
    (∃ (g' : Fin m → Pauli n) (c : Fin n → Fin n → Fin 3 → Fin 3 → Fin m → Bool),
      DegenLayoutSpec 4 1 2 (fun _ => {0, 1}) (toX g') (toZ g') c) ∨
    (∃ (g' : Fin m → Pauli n) (c : Fin n → Fin n → Fin 3 → Fin 3 → Fin m → Bool),
      DegenLayoutSpec 4 2 2 (fun _ => {0, 1}) (toX g') (toZ g') c) ∨
    (∃ (g' : Fin m → Pauli n) (c : Fin n → Fin n → Fin 3 → Fin 3 → Fin m → Bool),
      DegenLayoutSpec 4 2 3 (fun i => if i.val = 0 then {0, 1} else {1, 2})
      (toX g') (toZ g') c) ∨
    (∃ (g' : Fin m → Pauli n) (c : Fin n → Fin n → Fin 3 → Fin 3 → Fin m → Bool),
      DegenLayoutSpec 4 2 4 (fun i => if i.val = 0 then {0, 1} else {2, 3})
      (toX g') (toZ g') c) ∨
    (∃ r, 3 ≤ r ∧ r ≤ m ∧ ∃ (g' : Fin m → Pauli n)
      (c : Fin n → Fin n → Fin 3 → Fin 3 → Fin m → Bool), DegenGenSpec 4 r (toX g') (toZ g') c) := by
  obtain ⟨r, hr1, hrm, g1, hg1, hW1, hw1, hspan⟩ := dprep hg h2
  have hl1 : DNoWt1 g1 := fun v hv => h1 v (hspan ▸ hv)
  have hm0 : 0 < m := by omega
  obtain ⟨p, q, hpq, hpqs⟩ := wt2_supp (hw1 ⟨0, hm0⟩ (by simp only; omega))
  have h0 : ∀ i : Fin m, i.val = 0 → ∀ j, g1 i j ≠ 0 ↔ j = p ∨ j = q := fun i hi => by
    rw [show i = ⟨0, hm0⟩ from Fin.ext hi]; exact hpqs
  rcases (by omega : r = 1 ∨ r = 2 ∨ 3 ≤ r) with hr | hr | hr
  · subst hr
    left
    exact dpair hn hg1 hl1 hW1 hpq (fun i hi => h0 i (by omega))
  · subst hr
    have hm1 : 1 < m := by omega
    obtain ⟨p', q', hpq', hpqs'⟩ := wt2_supp (hw1 ⟨1, hm1⟩ (by simp only; omega))
    have h1' : ∀ i : Fin m, i.val = 1 → ∀ j, g1 i j ≠ 0 ↔ j = p' ∨ j = q' := fun i hi => by
      rw [show i = ⟨1, hm1⟩ from Fin.ext hi]; exact hpqs'
    by_cases hA : p = p' ∨ p = q' <;> by_cases hB : q = p' ∨ q = q'
    · right; left
      refine dpair hn hg1 hl1 hW1 hpq (fun i hi j => ?_)
      rcases (by omega : i.val = 0 ∨ i.val = 1) with hi0 | hi1
      · exact h0 i hi0 j
      · rw [h1' i hi1 j]
        rcases hA with hA | hA <;> rcases hB with hB | hB <;> subst hA <;> subst hB <;>
          first | exact absurd rfl hpq | exact absurd rfl hpq' | exact Iff.rfl | exact or_comm
    · right; right; left
      push Not at hB
      rcases hA with hA | hA
      · exact dchain hn hg1 hl1 hW1 (x := q) (y := p) (z := q') hpq.symm hB.2
          (by rw [hA]; exact hpq') (fun i hi j => (h0 i hi j).trans or_comm)
          (fun i hi j => by rw [h1' i hi j, hA])
      · exact dchain hn hg1 hl1 hW1 (x := q) (y := p) (z := p') hpq.symm hB.1
          (by rw [hA]; exact hpq'.symm) (fun i hi j => (h0 i hi j).trans or_comm)
          (fun i hi j => by rw [h1' i hi j, hA, or_comm])
    · right; right; left
      push Not at hA
      rcases hB with hB | hB
      · exact dchain hn hg1 hl1 hW1 (x := p) (y := q) (z := q') hpq hA.2
          (by rw [hB]; exact hpq') h0 (fun i hi j => by rw [h1' i hi j, hB])
      · exact dchain hn hg1 hl1 hW1 (x := p) (y := q) (z := p') hpq hA.1
          (by rw [hB]; exact hpq'.symm) h0 (fun i hi j => by rw [h1' i hi j, hB, or_comm])
    · right; right; right; left
      push Not at hA hB
      exact ddisj hn hg1 hl1 hW1 hpq hA.1 hA.2 hB.1 hB.2 hpq' h0 h1'
  · right; right; right; right
    exact ⟨r, hr, hrm, dgen hn hg1 hl1 hW1 hpq h0 hw1⟩

end LowWeight

