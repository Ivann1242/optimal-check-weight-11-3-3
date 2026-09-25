"""Generate the bv_decide lemma files LowWeight/SAT/*.lean.
usage: gen_sat.py n kind [r]   kind in pure | one | same | chain | disj | gen
"""
import sys
n = int(sys.argv[1]); kind = sys.argv[2]; m = n - 3; w = 4
SIMPA = """PureSpec, DegenLayoutSpec, DegenGenSpec, CommonSpec, Fin.forall_fin_succ,
      IsEmpty.forall_iff, Fin.isValue, Fin.succ_zero_eq_one, Fin.succ_one_eq_two"""
SIMPB = """Fin.lt_def, Fin.val_succ, Fin.val_zero, Fin.val_one, Fin.val_two, forall_const,
      true_and, and_true, false_implies, implies_true, not_false_eq_true, Fin.ext_iff"""
SIMPC = """rowWt, rowSymp, syn, colLt, colLe, funext_iff, SuppIs, SpanEq, ex, ez, Fin.sum_univ_succ,
      Fin.sum_univ_zero, Fin.forall_fin_succ, Fin.exists_fin_succ, IsEmpty.forall_iff,
      IsEmpty.exists_iff, Fin.isValue, Fin.succ_zero_eq_one, Fin.succ_one_eq_two"""
SIMPD = """Fin.lt_def, Fin.val_succ, Fin.val_zero, Fin.val_one, Fin.val_two, forall_const,
      true_and, and_true, false_implies, implies_true, not_false_eq_true, ite_true, ite_false,
      exists_false, or_false, false_or, Finset.mem_insert, Finset.mem_singleton,
      Finset.notMem_empty, decide_true, decide_false, Bool.true_and, Bool.false_and,
      Bool.or_false, Bool.false_or, Fin.ext_iff"""
LAYOUT = {'one': (1, 2, "fun _ => {0, 1}"),
          'same': (2, 2, "fun _ => {0, 1}"),
          'chain': (2, 3, "fun i => if i.val = 0 then {0, 1} else {1, 2}"),
          'disj': (2, 4, "fun i => if i.val = 0 then {0, 1} else {2, 3}")}
if kind == 'pure':
    name = f"pure_{n}"
    stmt = f"(x z : Fin {m} → Fin {n} → Bool) : ¬ PureSpec {w} x z"
elif kind in LAYOUT:
    r, tt, S = LAYOUT[kind]
    name = f"layout_{kind}_{n}"
    stmt = (f"(x z : Fin {m} → Fin {n} → Bool) (c : Fin {n} → Fin {n} → Fin 3 → Fin 3 → Fin {m} → Bool) :\n"
            f"    ¬ DegenLayoutSpec {w} {r} {tt} ({S}) x z c")
else:
    r = int(sys.argv[3]); name = f"gen_{n}_{r}"
    stmt = (f"(x z : Fin {m} → Fin {n} → Bool) (c : Fin {n} → Fin {n} → Fin 3 → Fin 3 → Fin {m} → Bool) :\n"
            f"    ¬ DegenGenSpec {w} {r} x z c")
PATCH = kind == "gen" and (n == 11 or (n == 10 and int(sys.argv[3]) <= 4))  # ofBool rewrite for the largest cases
if PATCH:
    SIMPD = SIMPD.replace("Fin.ext_iff", "Fin.ext_iff, ite_bv1")
out = f"""import LowWeight.Spec
import Std.Tactic.BVDecide

namespace LowWeight
set_option maxHeartbeats 0
set_option maxRecDepth 2000000
set_option linter.unusedSimpArgs false

theorem sat_{name} {stmt} := by
  intro h
  simp (config := {{maxSteps := 100000000}}) only [{SIMPA}] at h
  simp (config := {{decide := true, maxSteps := 100000000}}) only [{SIMPB}] at h
  simp (config := {{maxSteps := 100000000}}) only [{SIMPC}] at h
  simp (config := {{decide := true, maxSteps := 100000000}}) only [{SIMPD}] at h
  bv_decide (config := {{timeout := 36000, maxSteps := 100000000}})

end LowWeight"""
if PATCH:
    out = out.replace("set_option linter.unusedSimpArgs false\n", """set_option linter.unusedSimpArgs false

private theorem ite_bv1 (b : Bool) : (if b = true then (1 : BitVec 1) else 0) = BitVec.ofBool b := by
  cases b <;> rfl
""", 1)
print(out)
