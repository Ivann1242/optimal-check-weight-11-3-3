import LowWeight.Transport

/-! The pure case: a code of distance `≥ 3` whose stabilizer group has no element of weight
1 or 2 can be normalized to satisfy `PureSpec`. -/

namespace LowWeight

variable {m n : ℕ}

/-- No element of the span has weight 1 or 2. -/
def NoLow (g : Fin m → Pauli n) : Prop :=
  ∀ v ∈ Submodule.span F (Set.range g), wt v ≠ 1 ∧ wt v ≠ 2

theorem NoLow.map {g : Fin m → Pauli n} (T : Pauli n ≃ₗ[F] Pauli n)
    (hwt : ∀ v, wt (T v) = wt v) (h : NoLow g) : NoLow (fun i => T (g i)) := by
  intro v hv
  rw [mem_span_map_iff] at hv
  have hw : wt (T.symm v) = wt v := by rw [← hwt, T.apply_symm_apply]
  rw [← hw]; exact h _ hv

theorem synP_ne_of_noLow {f : Fin m → Pauli n} (hf : IsCode n m 4 f) (hl : NoLow f)
    {j l : Fin n} {t s : Fin 3} (h : j ≠ l ∨ t ≠ s) : synP f j t ≠ synP f l s := by
  intro he
  rw [synP_eq_iff] at he
  by_cases hjl : j = l
  · subst hjl
    have hts : t ≠ s := h.resolve_left (fun h' => h' rfl)
    have hw := wt_err_add_err_same j hts
    have hmem := hf.2.2.2 _ (by omega) (by omega) he
    exact (hl _ hmem).1 hw
  · have hw := wt_err_add_err hjl t s
    have hmem := hf.2.2.2 _ (by omega) (by omega) he
    exact (hl _ hmem).2 hw

theorem synP_nz_of_noLow {f : Fin m → Pauli n} (hf : IsCode n m 4 f) (hl : NoLow f)
    (j : Fin n) (t : Fin 3) : ∃ i, synP f j t i = true := by
  rw [synP_ne_zero_iff]
  by_contra hc
  push Not at hc
  have hw := wt_err j t
  have hmem := hf.2.2.2 _ (by omega) (by omega) hc
  exact (hl _ hmem).1 hw

theorem pure_spec {n m : ℕ} {g : Fin m → Pauli n} (hg : IsCode n m 4 g)
    (hlow : ∀ v ∈ Submodule.span F (Set.range g), wt v ≠ 1 ∧ wt v ≠ 2) :
    ∃ g' : Fin m → Pauli n, PureSpec 4 (toX g') (toZ g') := by
  have hl : NoLow g := hlow
  obtain ⟨M, hM⟩ := exists_localCanon g fun j =>
    ⟨synP_ne_of_noLow hg hl (Or.inr (by decide)), synP_ne_of_noLow hg hl (Or.inr (by decide)),
      synP_ne_of_noLow hg hl (Or.inr (by decide))⟩
  set g1 : Fin m → Pauli n := fun i => localP M (g i) with hg1
  have hg1c : IsCode n m 4 g1 := hg.localMap M
  have hl1 : NoLow g1 := hl.map (localP M) (wt_localP M)
  obtain ⟨τ, -, hτ⟩ := exists_sort_tail g1 0
  set g2 : Fin m → Pauli n := fun i => permP τ (g1 i) with hg2
  have hg2c : IsCode n m 4 g2 := hg1c.perm τ
  have hl2 : NoLow g2 := hl1.map (permP τ) (wt_permP τ)
  refine ⟨g2, ⟨⟨fun i => rowWt_le g2 i (hg2c.2.1 i) (by norm_num),
    fun i₁ i₂ => rowSymp_eq_zero g2 (hg2c.2.2.1 i₁ i₂),
    fun j t => synP_nz_of_noLow hg2c hl2 j t,
    fun j => ?_⟩, ?_, ?_⟩⟩
  · show colLt (synP g2 j 0) (synP g2 j 1) ∧ colLt (synP g2 j 1) (synP g2 j 2)
    rw [hg2, synP_permP, synP_permP, synP_permP]
    exact hM (τ j)
  · intro j l hjl t s
    have hne := synP_ne_of_noLow hg2c hl2 (t := t) (s := s) (Or.inl (ne_of_lt hjl))
    rw [Function.ne_iff] at hne
    exact hne
  · intro j l hjl
    have hne := synP_ne_of_noLow hg2c hl2 (j := j) (l := l) (t := 0) (s := 0)
      (Or.inl (fun h => by rw [h] at hjl; omega))
    exact colLt_of_colLe_of_ne (hτ j l (Nat.zero_le _) hjl) hne

end LowWeight
