/-
This test checks the Plan B query programs at the batched hash-vector sampler: the four
programs' theorems are axiom-clean, and the budgets evaluate to the values the theorems state.
It is not shipped: the verifier copies only `Construction*`, `Proof*` and `Submission`.

Run with `lake env lean tests/OracleProgramBudgets.lean`.
-/

import Construction.OraclePrograms

namespace Kriterion.ArgoMAC.Programs

open Kriterion.ArgoMAC.PlanB hiding coordinateBits

#print axioms garbleProgram_correct
#print axioms evaluateProgram_correct
#print axioms garbleBudget_eq
#print axioms evaluateBudget_eq
#print axioms laneGarbleBudget_closed
#print axioms laneEvalBudget_closed
#print axioms bounded_garbleM
#print axioms bounded_evaluateM

/-- The per-width fold budgets. -/
example : (hotGarbleBudget 2, hotGarbleBudget 4, hotGarbleBudget 5, hotEvalBudget 2,
    hotEvalBudget 4, hotEvalBudget 5) = (4, 28, 60, 2, 22, 52) := by
  rw [hotGarbleBudget_two, hotGarbleBudget_four, hotGarbleBudget_five, hotEvalBudget_two,
    hotEvalBudget_four, hotEvalBudget_five]

/-- The Benchmark-facing bounds are the proved budgets. -/
example : garbleQueries = garbleBudget := garbleBudget_eq.symm
example : evaluateQueries = evaluateBudget := evaluateBudget_eq.symm

-- The per-lane budgets `2,568 + 1,396 k` and `2,172 + 1,340 k` at `k = 4, 3, 452, 272`,
-- then the totals, computed by the compiled definitions (not by the closed forms).
#eval [Lane.curveX, Lane.curveY, Lane.pointX, Lane.pointY].map fun lane =>
  (limbCount lane, laneGarbleBudget lane, 2568 + 1396 * limbCount lane,
    laneEvalBudget lane, 2172 + 1340 * limbCount lane)
#eval (garbleBudget, garbleQueries)
#eval (evaluateBudget, evaluateQueries)

end Kriterion.ArgoMAC.Programs
