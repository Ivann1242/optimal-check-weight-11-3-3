import LowWeight.Spec
import Std.Tactic.BVDecide

namespace LowWeight
set_option maxHeartbeats 0
set_option maxRecDepth 2000000
set_option linter.unusedSimpArgs false

private theorem ite_bv1 (b : Bool) : (if b = true then (1 : BitVec 1) else 0) = BitVec.ofBool b := by
  cases b <;> rfl

theorem sat_gen_11_4 (x z : Fin 8 → Fin 11 → Bool) (c : Fin 11 → Fin 11 → Fin 3 → Fin 3 → Fin 8 → Bool) :
    ¬ DegenGenSpec 4 4 x z c := by
  intro h
  simp (config := {maxSteps := 100000000}) only [PureSpec, DegenLayoutSpec, DegenGenSpec, CommonSpec, Fin.forall_fin_succ,
      IsEmpty.forall_iff, Fin.isValue, Fin.succ_zero_eq_one, Fin.succ_one_eq_two] at h
  simp (config := {decide := true, maxSteps := 100000000}) only [Fin.lt_def, Fin.val_succ, Fin.val_zero, Fin.val_one, Fin.val_two, forall_const,
      true_and, and_true, false_implies, implies_true, not_false_eq_true, Fin.ext_iff] at h
  simp (config := {maxSteps := 100000000}) only [rowWt, rowSymp, syn, colLt, colLe, funext_iff, SuppIs, SpanEq, ex, ez, Fin.sum_univ_succ,
      Fin.sum_univ_zero, Fin.forall_fin_succ, Fin.exists_fin_succ, IsEmpty.forall_iff,
      IsEmpty.exists_iff, Fin.isValue, Fin.succ_zero_eq_one, Fin.succ_one_eq_two] at h
  simp (config := {decide := true, maxSteps := 100000000}) only [Fin.lt_def, Fin.val_succ, Fin.val_zero, Fin.val_one, Fin.val_two, forall_const,
      true_and, and_true, false_implies, implies_true, not_false_eq_true, ite_true, ite_false,
      exists_false, or_false, false_or, Finset.mem_insert, Finset.mem_singleton,
      Finset.notMem_empty, decide_true, decide_false, Bool.true_and, Bool.false_and,
      Bool.or_false, Bool.false_or, Fin.ext_iff, ite_bv1] at h
  bv_decide (config := {timeout := 36000, maxSteps := 100000000})

end LowWeight
