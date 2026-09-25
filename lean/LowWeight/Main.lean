import LowWeight.PureCase
import LowWeight.DegenCase
import LowWeight.Reduce
import LowWeight.SAT.Chain10
import LowWeight.SAT.Chain11
import LowWeight.SAT.Chain4
import LowWeight.SAT.Chain5
import LowWeight.SAT.Chain6
import LowWeight.SAT.Chain7
import LowWeight.SAT.Chain8
import LowWeight.SAT.Chain9
import LowWeight.SAT.Disj10
import LowWeight.SAT.Disj11
import LowWeight.SAT.Disj4
import LowWeight.SAT.Disj5
import LowWeight.SAT.Disj6
import LowWeight.SAT.Disj7
import LowWeight.SAT.Disj8
import LowWeight.SAT.Disj9
import LowWeight.SAT.Gen10_3
import LowWeight.SAT.Gen10_4
import LowWeight.SAT.Gen10_5
import LowWeight.SAT.Gen10_6
import LowWeight.SAT.Gen10_7
import LowWeight.SAT.Gen11_3
import LowWeight.SAT.Gen11_4
import LowWeight.SAT.Gen11_5
import LowWeight.SAT.Gen11_6
import LowWeight.SAT.Gen11_7
import LowWeight.SAT.Gen11_8
import LowWeight.SAT.Gen6_3
import LowWeight.SAT.Gen7_3
import LowWeight.SAT.Gen7_4
import LowWeight.SAT.Gen8_3
import LowWeight.SAT.Gen8_4
import LowWeight.SAT.Gen8_5
import LowWeight.SAT.Gen9_3
import LowWeight.SAT.Gen9_4
import LowWeight.SAT.Gen9_5
import LowWeight.SAT.Gen9_6
import LowWeight.SAT.One10
import LowWeight.SAT.One11
import LowWeight.SAT.One4
import LowWeight.SAT.One5
import LowWeight.SAT.One6
import LowWeight.SAT.One7
import LowWeight.SAT.One8
import LowWeight.SAT.One9
import LowWeight.SAT.Pure10
import LowWeight.SAT.Pure11
import LowWeight.SAT.Pure4
import LowWeight.SAT.Pure5
import LowWeight.SAT.Pure6
import LowWeight.SAT.Pure7
import LowWeight.SAT.Pure8
import LowWeight.SAT.Pure9
import LowWeight.SAT.Same10
import LowWeight.SAT.Same11
import LowWeight.SAT.Same4
import LowWeight.SAT.Same5
import LowWeight.SAT.Same6
import LowWeight.SAT.Same7
import LowWeight.SAT.Same8
import LowWeight.SAT.Same9

/-!
# Main theorem: no `[[11,3,3]]` stabilizer code has generators of weight at most four

QIQCOP problem op_458e9e86. We prove, for `4 ≤ N ≤ 11`, that no `[[N,3,≥3]]` code has a generating
set of weight `≤ 4`, by induction on `N`. A code falls into exactly one case:
* its stabilizer contains a weight-one element: delete that qubit (`IsCode.reduce_weight_one`);
* weight-two elements but no weight-one element: normalize (`degen_spec`) and refute the resulting
  Boolean specification with `bv_decide` (files `LowWeight/SAT/*`);
* no element of weight `≤ 2` (pure code): normalize (`pure_spec`) and refute with `bv_decide`.
-/

namespace LowWeight

theorem step {n m : ℕ} (hn : 3 ≤ n)
    (hpure : ∀ x z : Fin (m+1) → Fin (n+1) → Bool, ¬ PureSpec 4 x z)
    (hone : ∀ (x z : Fin (m+1) → Fin (n+1) → Bool) c,
      ¬ DegenLayoutSpec 4 1 2 (fun _ => ({0, 1} : Finset (Fin (n+1)))) x z c)
    (hsame : ∀ (x z : Fin (m+1) → Fin (n+1) → Bool) c,
      ¬ DegenLayoutSpec 4 2 2 (fun _ => ({0, 1} : Finset (Fin (n+1)))) x z c)
    (hchain : ∀ (x z : Fin (m+1) → Fin (n+1) → Bool) c,
      ¬ DegenLayoutSpec 4 2 3
        (fun i : Fin (m+1) => if i.val = 0 then ({0, 1} : Finset (Fin (n+1))) else {1, 2}) x z c)
    (hdisj : ∀ (x z : Fin (m+1) → Fin (n+1) → Bool) c,
      ¬ DegenLayoutSpec 4 2 4
        (fun i : Fin (m+1) => if i.val = 0 then ({0, 1} : Finset (Fin (n+1))) else {2, 3}) x z c)
    (hgen : ∀ r, 3 ≤ r → r ≤ m + 1 → ∀ (x z : Fin (m+1) → Fin (n+1) → Bool) c,
      ¬ DegenGenSpec 4 r x z c)
    (hprev : ∀ h : Fin m → Pauli n, ¬ IsCode n m 4 h)
    (g : Fin (m+1) → Pauli (n+1)) : ¬ IsCode (n+1) (m+1) 4 g := by
  intro hg
  by_cases h1 : ∃ v ∈ Submodule.span F (Set.range g), wt v = 1
  · obtain ⟨v, hv, hw⟩ := h1
    obtain ⟨h, hh⟩ := hg.reduce_weight_one v hv hw
    exact hprev h hh
  have h1' : ∀ v ∈ Submodule.span F (Set.range g), wt v ≠ 1 := fun v hv hw => h1 ⟨v, hv, hw⟩
  by_cases h2 : ∃ v ∈ Submodule.span F (Set.range g), wt v = 2
  · rcases degen_spec (by omega) hg h1' h2 with
      ⟨g', c, h⟩ | ⟨g', c, h⟩ | ⟨g', c, h⟩ | ⟨g', c, h⟩ | ⟨r, hr3, hrm, g', c, h⟩
    · exact hone _ _ _ h
    · exact hsame _ _ _ h
    · exact hchain _ _ _ h
    · exact hdisj _ _ _ h
    · exact hgen r hr3 hrm _ _ _ h
  · obtain ⟨g', h⟩ := pure_spec hg fun v hv => ⟨h1' v hv, fun hw => h2 ⟨v, hv, hw⟩⟩
    exact hpure _ _ h

theorem noCode_3 (g : Fin 0 → Pauli 3) : ¬ IsCode 3 0 4 g := not_isCode_zero (by norm_num) g

theorem noCode_4 (g : Fin 1 → Pauli 4) : ¬ IsCode 4 1 4 g :=
  step (n := 3) (m := 0) (by norm_num) sat_pure_4 sat_layout_one_4 sat_layout_same_4
    sat_layout_chain_4 sat_layout_disj_4
    (fun r h3 hr => by omega)
    noCode_3 g

theorem noCode_5 (g : Fin 2 → Pauli 5) : ¬ IsCode 5 2 4 g :=
  step (n := 4) (m := 1) (by norm_num) sat_pure_5 sat_layout_one_5 sat_layout_same_5
    sat_layout_chain_5 sat_layout_disj_5
    (fun r h3 hr => by omega)
    noCode_4 g

theorem noCode_6 (g : Fin 3 → Pauli 6) : ¬ IsCode 6 3 4 g :=
  step (n := 5) (m := 2) (by norm_num) sat_pure_6 sat_layout_one_6 sat_layout_same_6
    sat_layout_chain_6 sat_layout_disj_6
    (fun r h3 hr x z c => by
      interval_cases r
      · exact sat_gen_6_3 x z c)
    noCode_5 g

theorem noCode_7 (g : Fin 4 → Pauli 7) : ¬ IsCode 7 4 4 g :=
  step (n := 6) (m := 3) (by norm_num) sat_pure_7 sat_layout_one_7 sat_layout_same_7
    sat_layout_chain_7 sat_layout_disj_7
    (fun r h3 hr x z c => by
      interval_cases r
      · exact sat_gen_7_3 x z c
      · exact sat_gen_7_4 x z c)
    noCode_6 g

theorem noCode_8 (g : Fin 5 → Pauli 8) : ¬ IsCode 8 5 4 g :=
  step (n := 7) (m := 4) (by norm_num) sat_pure_8 sat_layout_one_8 sat_layout_same_8
    sat_layout_chain_8 sat_layout_disj_8
    (fun r h3 hr x z c => by
      interval_cases r
      · exact sat_gen_8_3 x z c
      · exact sat_gen_8_4 x z c
      · exact sat_gen_8_5 x z c)
    noCode_7 g

theorem noCode_9 (g : Fin 6 → Pauli 9) : ¬ IsCode 9 6 4 g :=
  step (n := 8) (m := 5) (by norm_num) sat_pure_9 sat_layout_one_9 sat_layout_same_9
    sat_layout_chain_9 sat_layout_disj_9
    (fun r h3 hr x z c => by
      interval_cases r
      · exact sat_gen_9_3 x z c
      · exact sat_gen_9_4 x z c
      · exact sat_gen_9_5 x z c
      · exact sat_gen_9_6 x z c)
    noCode_8 g

theorem noCode_10 (g : Fin 7 → Pauli 10) : ¬ IsCode 10 7 4 g :=
  step (n := 9) (m := 6) (by norm_num) sat_pure_10 sat_layout_one_10 sat_layout_same_10
    sat_layout_chain_10 sat_layout_disj_10
    (fun r h3 hr x z c => by
      interval_cases r
      · exact sat_gen_10_3 x z c
      · exact sat_gen_10_4 x z c
      · exact sat_gen_10_5 x z c
      · exact sat_gen_10_6 x z c
      · exact sat_gen_10_7 x z c)
    noCode_9 g

theorem noCode_11 (g : Fin 8 → Pauli 11) : ¬ IsCode 11 8 4 g :=
  step (n := 10) (m := 7) (by norm_num) sat_pure_11 sat_layout_one_11 sat_layout_same_11
    sat_layout_chain_11 sat_layout_disj_11
    (fun r h3 hr x z c => by
      interval_cases r
      · exact sat_gen_11_3 x z c
      · exact sat_gen_11_4 x z c
      · exact sat_gen_11_5 x z c
      · exact sat_gen_11_6 x z c
      · exact sat_gen_11_7 x z c
      · exact sat_gen_11_8 x z c)
    noCode_10 g

/-- **QIQCOP op_458e9e86 (negative answer).** There is no qubit stabilizer code with parameters
`[[11,3,d]]`, `d ≥ 3`, whose stabilizer group is generated by eight independent commuting Pauli
operators of weight at most four (Eq. (458e-conditions) of the problem statement). -/
theorem no_weight_four_11_3_3 : ¬ ∃ g : Fin 8 → Pauli 11, IsCode 11 8 4 g :=
  fun ⟨g, hg⟩ => noCode_11 g hg

end LowWeight
