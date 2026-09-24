/-
**The two sanctioned large-numeral facts** of the phase-4 preimage sampler (design A1 §4.4).

* `preimageAccept_nat : (7 · 2^326 + 10) · p^455 ≤ 10 · 2^115712` (an *upper* bound on `p^455`):
  at most `3/10` of the `2^326` multipliers `t` push `enc + p^455 · t` past `2^115712`, whatever
  `enc < p^455`;
* `preimageComplete_nat : 2^115712 ≤ 2^326 · p^455` (a *lower* bound on `p^455`): every `t` with
  `enc + p^455 · t < 2^115712` is below `2^326`, so the `326`-bit draw covers the whole fibre. The
  margin is `log₂ (2^115712 / p^455) ≈ 325.505`, too thin for exponent arithmetic from `p ≥ 2^253`.

Both are closed by the kernel's GMP-accelerated `Nat.pow`/`Nat.ble` (`decide +kernel`; the
elaborator-side `Nat.le_of_ble_eq_true rfl` exceeds its recursion limit). They are the
controller's two sanctioned exceptions to the no-large-numerals rule; their build memory is
measured in `phase4-notes/T9a-report.md` (within a few MB of a trivial module with the same
import). Nothing else in the tree evaluates a power at the `p^455` scale.
-/

import Construction.Simulator.Layout

namespace Kriterion.ArgoMAC.PlanB.SimMachine

/-- **The acceptance inequality**, by kernel evaluation. -/
theorem preimageAccept_nat : (7 * 2 ^ 326 + 10) * pNat ^ 455 ≤ 10 * 2 ^ 115712 :=
  by decide +kernel

/-- **The fibre-coverage inequality**, by kernel evaluation. -/
theorem preimageComplete_nat : 2 ^ 115712 ≤ 2 ^ 326 * pNat ^ 455 :=
  by decide +kernel

end Kriterion.ArgoMAC.PlanB.SimMachine
