import LowWeight.Basic

namespace LowWeight

open Submodule

theorem IsCode.exchange {n m r w : ℕ} {g : Fin m → Pauli n} (hg : IsCode n m w g)
    (b : Fin r → Pauli n) (hb : LinearIndependent F b)
    (hbs : ∀ i, b i ∈ Submodule.span F (Set.range g)) (hbw : ∀ i, wt (b i) ≤ w) :
    ∃ (hr : r ≤ m) (g' : Fin m → Pauli n), IsCode n m w g' ∧
      (∀ i : Fin r, g' (Fin.castLE hr i) = b i) ∧
      Submodule.span F (Set.range g') = Submodule.span F (Set.range g) := by
  classical
  obtain ⟨hli, hw, hc, hd⟩ := hg
  have hbinj : Function.Injective b := hb.injective
  -- The `DivisionRing`-based extension lemma needs the module structure stated over the
  -- field's semiring; we supply it explicitly and restate the conclusions.
  obtain ⟨B, hBt, hbB, htB0, hBli0⟩ :=
    @exists_linearIndepOn_id_extension F (Pauli n) _ _ (inferInstance : Module F (Pauli n)) _ _
      hb.linearIndepOn_id (Set.subset_union_left : Set.range b ⊆ Set.range b ∪ Set.range g)
  have htB : Set.range b ∪ Set.range g ⊆ span F B := htB0
  have hBli : LinearIndepOn F id B := hBli0
  have hBS : span F B = span F (Set.range g) := by
    apply le_antisymm
    · rw [span_le]; intro x hx
      rcases hBt hx with ⟨i, rfl⟩ | ⟨i, rfl⟩
      · exact hbs i
      · exact subset_span ⟨i, rfl⟩
    · rw [span_le]; intro x hx; exact htB (Or.inr hx)
  have hBmem : ∀ x ∈ B, x ∈ span F (Set.range g) ∧ wt x ≤ w := by
    intro x hx
    rcases hBt hx with ⟨i, rfl⟩ | ⟨i, rfl⟩
    · exact ⟨hbs i, hbw i⟩
    · exact ⟨subset_span ⟨i, rfl⟩, hw i⟩
  have hcardB : B.ncard = m := by
    have h1 := finrank_span_eq_card (R := F) hBli.linearIndependent
    have h2 := finrank_span_eq_card hli
    rw [show (Set.range fun x : B => id (x : Pauli n)) = B from Subtype.range_coe] at h1
    rw [hBS, h2, Fintype.card_fin] at h1
    rw [← Nat.card_coe_set_eq, Nat.card_eq_fintype_card, ← h1]
  have hcardb : (Set.range b).ncard = r := by
    rw [← Nat.card_coe_set_eq, Nat.card_eq_fintype_card, Set.card_range_of_injective hbinj,
      Fintype.card_fin]
  have hr : r ≤ m := by
    rw [← hcardB, ← hcardb]; exact Set.ncard_le_ncard hbB (Set.toFinite B)
  refine ⟨hr, ?_⟩
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hr
  set D := B \ Set.range b with hD
  have hcardD : Fintype.card D = k := by
    rw [← Nat.card_eq_fintype_card, Nat.card_coe_set_eq, hD,
      Set.ncard_sdiff hbB (Set.toFinite _), hcardB, hcardb]
    omega
  let e : Fin k ≃ D := (Fintype.equivFinOfCardEq hcardD).symm
  let c : Fin k → Pauli n := fun j => (e j).1
  have hcinj : Function.Injective c := fun i j h => e.injective (Subtype.ext h)
  have hcD : ∀ j, c j ∈ D := fun j => (e j).2
  let g' : Fin (r + k) → Pauli n := Fin.append b c
  have hinj : Function.Injective g' := by
    intro i j h
    induction i using Fin.addCases with
    | left i =>
      induction j using Fin.addCases with
      | left j => simp [g', Fin.append_left] at h; rw [hbinj h]
      | right j =>
        simp [g', Fin.append_left, Fin.append_right] at h
        exact absurd ⟨i, h⟩ (hcD j).2
    | right i =>
      induction j using Fin.addCases with
      | left j =>
        simp [g', Fin.append_left, Fin.append_right] at h
        exact absurd ⟨j, h.symm⟩ (hcD i).2
      | right j => simp [g', Fin.append_right] at h; rw [hcinj h]
  have hrange : Set.range g' = B := by
    ext x
    constructor
    · rintro ⟨i, rfl⟩
      induction i using Fin.addCases with
      | left i => simp only [g', Fin.append_left]; exact hbB ⟨i, rfl⟩
      | right j => simp only [g', Fin.append_right]; exact (hcD j).1
    · intro hx
      by_cases hxb : x ∈ Set.range b
      · obtain ⟨i, rfl⟩ := hxb
        exact ⟨Fin.castAdd k i, by simp [g', Fin.append_left]⟩
      · have hxD : x ∈ D := ⟨hx, hxb⟩
        refine ⟨Fin.natAdd r (e.symm ⟨x, hxD⟩), ?_⟩
        simp [g', Fin.append_right, c]
  have hspan : span F (Set.range g') = span F (Set.range g) := by rw [hrange, hBS]
  have hmem : ∀ i, g' i ∈ B := fun i => hrange ▸ ⟨i, rfl⟩
  refine ⟨g', ⟨?_, ?_, ?_, ?_⟩, ?_, hspan⟩
  · exact (linearIndepOn_id_range_iff hinj).mp (hrange ▸ hBli)
  · exact fun i => (hBmem _ (hmem i)).2
  · exact fun i j => symp_span_span hc (hBmem _ (hmem i)).1 (hBmem _ (hmem j)).1
  · intro v h1 h2 hv
    rw [hspan]
    apply hd v h1 h2
    intro j
    exact symp_eq_zero_of_mem_span hv (hspan ▸ subset_span ⟨j, rfl⟩)
  · intro i
    have : (Fin.castLE hr i : Fin (r + k)) = Fin.castAdd k i := Fin.ext rfl
    rw [this]; simp [g', Fin.append_left]

theorem IsCode.exchange_one {n m w : ℕ} {g : Fin (m+1) → Pauli n} (hg : IsCode n (m+1) w g)
    (e : Pauli n) (he0 : e ≠ 0)
    (he : e ∈ Submodule.span F (Set.range g)) (hew : wt e ≤ w) :
    ∃ g' : Fin (m+1) → Pauli n, IsCode n (m+1) w g' ∧ g' 0 = e ∧
      Submodule.span F (Set.range g') = Submodule.span F (Set.range g) := by
  have hlin : LinearIndependent F (fun _ : Fin 1 => e) := by
    refine (@Fintype.linearIndependent_iff (Fin 1) F (Pauli n) _ _ (inferInstance : Module F (Pauli n)) _ _).mpr ?_
    intro c hc i
    have h0 : c 0 = 0 := by
      rcases (by decide : ∀ a : F, a = 0 ∨ a = 1) (c 0) with h | h
      · exact h
      · exfalso; apply he0
        simp only [Finset.univ_unique, Fin.default_eq_zero, Finset.sum_singleton, h,
          one_smul] at hc
        exact hc
    rw [Subsingleton.elim i 0]; exact h0
  obtain ⟨hr, g', hg', hb, hs⟩ := hg.exchange (fun _ : Fin 1 => e) hlin (fun _ => he) (fun _ => hew)
  exact ⟨g', hg', hb 0, hs⟩

end LowWeight
