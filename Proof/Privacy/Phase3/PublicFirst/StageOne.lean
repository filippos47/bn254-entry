/-
**Phase 3, P1d — the garbler's EncPRF entries, to be planted after `G1U`'s stage 1.**

`G1U` (`hiddenDeletedHybrid`) runs the adversary's first stage on the lazy oracle holding the
garbler's EncPRF entries (`encEntries`, EncPRF pairs only: `encEntries_encOnly`). Its later form
(`Lift.g1uLaterWith`) runs stage 1 on the empty oracle, stops (`none`) at the first query that
touches one of those entries (`runFlag`, `EncTouch`), and plants them only at the input choice,
before the installed entries.

`G1U` is above its later form for any install rule (`Lift.below_laterWith`, for each bit the later
form's untouched mass is at most `G1U`'s). The touch mass is the stage-1 EncPRF charge of
`publicFirst`: at most `4/2^128` per stage-1 EncPRF query once the planted pairs are independent of
the stage-1 view.
-/

import Proof.Privacy.Phase3.PublicFirst.Install

set_option linter.unusedSectionVars false

namespace Kriterion.ArgoMAC.Security.Phase3.PublicFirst

open BN254 Cryptography GarbledCircuit Kriterion.ArgoMAC.PlanB
open Kriterion.ArgoMAC.Scheme (Coins Oracle)
open Kriterion.ArgoMAC.Phase3.Glue (PlanBAdversary)
open scoped ENNReal

noncomputable section

/-- The garbler's EncPRF entries on a tape. -/
def encEntries [FieldCertificate] [GroupCertificate] (scalar : NonZeroScalar)
    (tape : Coins × Oracle) : List (Entry FixedIndex EncPRF.PermutationIndex) :=
  (garblerTranscript scalar tape).filter Entry.IsEnc

theorem encEntries_encOnly [FieldCertificate] [GroupCertificate] (scalar : NonZeroScalar)
    (tape : Coins × Oracle) : ∀ entry ∈ encEntries scalar tape, (encPair entry).isSome := by
  intro entry member
  have isEnc := (List.mem_filter.mp member).2
  obtain ⟨request, answer⟩ := entry
  cases request <;> simp_all [Entry.IsEnc, encPair]

end

end Kriterion.ArgoMAC.Security.Phase3.PublicFirst
