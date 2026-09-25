/-
**The two sanctioned large-numeral facts** of the phase-4 preimage sampler (design A1 §4.4).

* `preimageAccept_nat : (7 · 2^363 + 10) · p^364 ≤ 10 · 2^92672` (an *upper* bound on `p^364`):
  at most `3/10` of the `2^363` multipliers `t` push `enc + p^364 · t` past `2^92672`, whatever
  `enc < p^364`;
* `preimageComplete_nat : 2^92672 ≤ 2^363 · p^364` (a *lower* bound on `p^364`): every `t` with
  `enc + p^364 · t < 2^92672` is below `2^363`, so the `363`-bit draw covers the whole fibre. The
  margin is `log₂ (2^92672 / p^364) ≈ 362.804`, too thin for exponent arithmetic from `p ≥ 2^253`.

Both are closed by the kernel's GMP-accelerated `Nat.pow`/`Nat.ble` (`decide +kernel`; the
elaborator-side `Nat.le_of_ble_eq_true rfl` exceeds its recursion limit). They are the
controller's two sanctioned exceptions to the no-large-numerals rule. Nothing else in the tree
evaluates a power at the `p^364` scale.
-/

import Construction.Simulator.Layout

namespace Kriterion.ArgoMAC.PlanB.SimMachine

/-- **The acceptance inequality**, by kernel evaluation. -/
theorem preimageAccept_nat : (7 * 2 ^ 363 + 10) * pNat ^ 364 ≤ 10 * 2 ^ 92672 :=
  by decide +kernel

/-- **The fibre-coverage inequality**, by kernel evaluation. -/
theorem preimageComplete_nat : 2 ^ 92672 ≤ 2 ^ 363 * pNat ^ 364 :=
  by decide +kernel

end Kriterion.ArgoMAC.PlanB.SimMachine
