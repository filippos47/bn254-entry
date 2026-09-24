/-
**Phase 3, P1c — step 1: the garbler's switch-mask vectors are determined by its transcript.**

`maskOf_determined`: an oracle that agrees with the garbler's transcript on a tape gives the same
garbler vectors (`MaskSwap.garblerMask` at `garblerKeys`, i.e. the batched hash answers at the
garbler's own one-hot labels). The transcript of a bind is the concatenation (`transcriptOf_bind`),
so agreement with the whole transcript propagates to every stage of `Programs.garbleM`
(`agrees_bind`): the bridge hash at `bridgeInput t`, the pads, and each lane's tables, whose vectors
are `garblerMask` (`eval_laneM`).
-/

import Proof.Privacy.Phase3.Hidden.Resample
import Proof.Privacy.Phase3.GameSwap

set_option maxRecDepth 8000
set_option linter.unusedSectionVars false

namespace Kriterion.ArgoMAC.Security.Phase3.Hidden

open BN254 Cryptography Kriterion.ArgoMAC.PlanB
open Kriterion.ArgoMAC.Scheme (Coins Oracle)

noncomputable section

variable {FixedIndex' EncIndex' : Type} [DecidableEq FixedIndex'] [DecidableEq EncIndex']

theorem transcriptOf_bind {α β : Type} (answer : ∀ query : PublicQuery FixedIndex' EncIndex', query.Answer)
    (program : FreeQuery (publicOracleSpec FixedIndex' EncIndex') α)
    (next : α → FreeQuery (publicOracleSpec FixedIndex' EncIndex') β) :
    transcriptOf answer (program >>= next) =
      transcriptOf answer program ++ transcriptOf answer (next (program.eval answer)) := by
  induction program with
  | pure value => rfl
  | query request rest ih =>
      show ⟨request, answer request⟩ :: transcriptOf answer (FreeQuery.bind (rest (answer request)) next) = _
      rw [show FreeQuery.bind (rest (answer request)) next = rest (answer request) >>= next from rfl,
        ih]
      rfl

/-- Agreement with a bind's transcript: the first stage evaluates the same, and the rest agrees. -/
theorem agrees_bind {α β : Type} (program : FreeQuery (publicOracleSpec FixedIndex' EncIndex') α)
    (next : α → FreeQuery (publicOracleSpec FixedIndex' EncIndex') β)
    (first second : PublicOracle FixedIndex' EncIndex')
    (agrees : AgreesWith second (transcriptOf (publicAnswer first) (program >>= next))) :
    program.eval (publicAnswer second) = program.eval (publicAnswer first) ∧
      AgreesWith second (transcriptOf (publicAnswer first) (next (program.eval (publicAnswer first)))) := by
  rw [transcriptOf_bind] at agrees
  refine ⟨(transcriptOf_of_agrees program first second
    (fun entry member => agrees entry (List.mem_append_left _ member))).2,
    fun entry member => agrees entry (List.mem_append_right _ member)⟩

/-- **Invariance passes from one mixture to another** of the same mask-separated components, when the
kernel preserves the mask and the first mixture has full support. -/
theorem mixture_invariant {T M : Type} (ρ ρ' : PMF M) (κ : M → PMF T) (K : T → PMF T)
    (mask : T → M) (full : ∀ m, ρ' m ≠ 0)
    (supported : ∀ m t, t ∈ (κ m).support → mask t = m)
    (preserves : ∀ t t', t' ∈ (K t).support → mask t' = mask t)
    (invariant : (ρ'.bind κ).bind K = ρ'.bind κ) :
    (ρ.bind κ).bind K = ρ.bind κ := by
  have zeroMoved : ∀ m t, mask t ≠ m → ((κ m).bind K) t = 0 := by
    intro m t ne
    rw [PMF.bind_apply]
    refine ENNReal.tsum_eq_zero.mpr fun s => ?_
    by_cases hs : κ m s = 0
    · rw [hs, zero_mul]
    · by_cases ht : K s t = 0
      · rw [ht, mul_zero]
      · exfalso
        have maskS := supported m s ((PMF.mem_support_iff _ _).mpr hs)
        have maskT := preserves s t ((PMF.mem_support_iff _ _).mpr ht)
        exact ne (maskT.trans maskS)
  have zeroStay : ∀ m t, mask t ≠ m → κ m t = 0 := by
    intro m t ne
    by_contra hs
    exact ne (supported m t ((PMF.mem_support_iff _ _).mpr hs))
  have each : ∀ m₀, (κ m₀).bind K = κ m₀ := by
    intro m₀
    ext t
    by_cases hm : mask t = m₀
    · have atT := congrArg (fun law : PMF T => law t) invariant
      simp only [PMF.bind_bind] at atT
      rw [PMF.bind_apply, PMF.bind_apply] at atT
      rw [tsum_eq_single m₀ (fun m ne => by rw [zeroMoved m t (hm.trans_ne (Ne.symm ne)), mul_zero]),
        tsum_eq_single m₀ (fun m ne => by rw [zeroStay m t (hm.trans_ne (Ne.symm ne)), mul_zero])]
        at atT
      exact (ENNReal.mul_right_inj (full m₀) (PMF.apply_ne_top _ _)).mp atT
    · rw [zeroMoved m₀ t hm, zeroStay m₀ t hm]
  rw [PMF.bind_bind]
  exact congrArg (PMF.bind ρ) (funext each)

section PlanB

variable [FieldCertificate] [GroupCertificate]

/-- The garbler's switch-mask vectors on a tape (`MaskSwap.garblerMask` at the garbler's own
keys). -/
def maskOf (tape : Coins × Oracle) : MaskVectors :=
  garblerMask tape.2.1 tape.2.2.2 (garblerKeys (tape.1, tape.2.1, tape.2.2.1) tape.2.2.2).1
    (garblerKeys (tape.1, tape.2.1, tape.2.2.1) tape.2.2.2).2

/-- One lane's garbler vectors are its tables' masks. -/
theorem garblerMask_laneTables (fixed : PermutationOracle FixedIndex Block)
    (hash : EncPRF.HashOracle) (delta : Lane → Block)
    (bitKey : Lane → Fin PlanB.coordinateBits → Block × Block) (lane : Lane) (chunk : Fin chunkCount)
    (switch : Fin (2 ^ chunkWidth chunk)) :
    garblerMask fixed hash delta bitKey ⟨lane, chunk, switch⟩ =
      (Programs.laneTables fixed hash lane (delta lane) (bitKey lane)).masks chunk switch := rfl

/-- **The masks are determined by the garbler's transcript.** -/
theorem maskOf_determined (coins : Coins) (first second : Oracle) (scalar : NonZeroScalar)
    (agrees : AgreesWith second (transcriptOf (publicAnswer first) (Programs.garbleM scalar coins))) :
    maskOf (coins, second) = maskOf (coins, first) := by
  unfold Programs.garbleM at agrees
  dsimp only at agrees
  obtain ⟨hashSame, agrees⟩ := agrees_bind _ _ first second agrees
  obtain ⟨padsSame, agrees⟩ := agrees_bind _ _ first second agrees
  obtain ⟨curveXSame, agrees⟩ := agrees_bind _ _ first second agrees
  obtain ⟨curveYSame, agrees⟩ := agrees_bind _ _ first second agrees
  obtain ⟨pointXSame, agrees⟩ := agrees_bind _ _ first second agrees
  obtain ⟨pointYSame, _⟩ := agrees_bind _ _ first second agrees
  simp only [Programs.eval_askHash] at hashSame
  simp only [Programs.eval_padsM, Programs.eval_askHash] at padsSame pointXSame pointYSame
  rw [Programs.eval_laneM, Programs.eval_laneM] at curveXSame curveYSame pointXSame pointYSame
  have whitened : Pipeline.whitenedKey second.2.1 second.2.2 coins.bridgeKey coins.inputMacKey =
      Pipeline.whitenedKey first.2.1 first.2.2 coins.bridgeKey coins.inputMacKey := by
    unfold Pipeline.whitenedKey
    rw [← Programs.whitenKeyOf_realPads, ← Programs.whitenKeyOf_realPads]
    unfold EncPRF.whiteningKeys
    rw [hashSame]
    exact congrArg (fun pads => Programs.whitenKeyOf pads coins.inputMacKey) padsSame
  have white : Pipeline.whitenedKey first.2.1 first.2.2 coins.bridgeKey coins.inputMacKey =
      EncPRF.whitenKey first.2.1 ⟨(first.2.2 (bridgeInput coins.bridgeKey)).1,
        (first.2.2 (bridgeInput coins.bridgeKey)).2⟩ coins.inputMacKey := rfl
  funext site
  obtain ⟨lane, chunk, switch⟩ := site
  unfold maskOf
  rw [garblerMask_laneTables, garblerMask_laneTables]
  cases lane with
  | curveX =>
      simp only [garblerKeys, Lane.coord]
      rw [curveXSame]
  | curveY =>
      simp only [garblerKeys, Lane.coord]
      rw [curveYSame]
  | pointX =>
      simp only [garblerKeys, Lane.coord]
      rw [Programs.whitenKeyOf_realPads] at pointXSame
      rw [whitened, white, pointXSame]
  | pointY =>
      simp only [garblerKeys, Lane.coord]
      rw [Programs.whitenKeyOf_realPads] at pointYSame
      rw [whitened, white, pointYSame]

end PlanB

end

end Kriterion.ArgoMAC.Security.Phase3.Hidden
