/-
**Phase 3, P1d — flagged games and the overlap bound.**

The flag-mass part of `G1U → HW`'s constant (`4q₁/2^128 + 364/(r−1)`) cannot be reached by a
triangle of advantage bounds through an intermediate game: `G1U` and `HW` each deviate from any
middle game on stage-1 touches of the *same* (coupled) stage-2 points, and a triangle charges those
touches twice.
The chain is therefore run on **flagged** games, `PMF (Option Bool)` with `none` the bad event:

* `Below first flagged` — `flagged (some b) ≤ first b` for both bits: the flag-down part of
  `flagged` is below `first`;
* `Below.trans` / `FlagMono` — lower bounds compose, and raising more flags only lowers the
  flag-down part;
* `flagged_total` — the three masses of a flagged game sum to one.

The overlap bound itself is `MiddleOff.advantage_le_of_overlap_tv`: two games above two flagged
games are within the first's flag mass plus the flagged games' total-variation distance. So the
two chains from `G1U` and from `HW` meet at flagged middle games whose flag is the *union* of both
sides' bad events (each stage-1 query charged once, at its index, against the coupled stage-2
points there).
-/

import Proof.Privacy.Phase3.UntilBadIff

set_option linter.unusedSectionVars false

namespace Kriterion.ArgoMAC.Security.Phase3.PublicFirst

open Cryptography
open scoped ENNReal

noncomputable section

/-- The flag-down part of a flagged game is below a game. -/
def Below (game : PMF Bool) (flagged : PMF (Option Bool)) : Prop :=
  ∀ b, flagged (some b) ≤ game b

/-- A flagged game is below another (more flags raised): its flag-down part is smaller. -/
def FlagMono (upper lower : PMF (Option Bool)) : Prop :=
  ∀ b, lower (some b) ≤ upper (some b)

theorem Below.trans {game : PMF Bool} {upper lower : PMF (Option Bool)} (below : Below game upper)
    (mono : FlagMono upper lower) : Below game lower :=
  fun b => (mono b).trans (below b)

/-- The three masses of a flagged game sum to one. -/
theorem flagged_total (flagged : PMF (Option Bool)) :
    flagged none + flagged (some true) + flagged (some false) = 1 := by
  have total := flagged.tsum_coe
  rw [tsum_fintype] at total
  rw [← total]
  simp only [Fintype.sum_option, Fintype.sum_bool]
  ring

end

end Kriterion.ArgoMAC.Security.Phase3.PublicFirst
