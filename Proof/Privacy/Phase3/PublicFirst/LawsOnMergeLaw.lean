/-
**Phase 3, P1q — `LawOn`, step (D5), part 2: the private side of `LawOn`, as one average.**

Assembling (D2) `opening_eager`, (D3) `install_state`, (D4) `shadow_installed_eager` and the merge
(`completion_overlay_transcript`, `overlayProg_spec`, `merge_resample`):

**`lawOn_private`**: the left side of `LawOn` (with its weight written `r.elim 0 (Ψ P L)`) equals

```
onPrivForm = E_source E_{T ~ uniformMaskTape} E_{O uniform} mergeK T (v(T, O)) O,
mergeK T v O = E_{coins} E_{r ~ limbsOf v coins} [r = some limbs ↦
  E_{δ ~ deltaLaw} revealWeight coins δ Ψ (onView P u mac (overlay (installTape u T limbs) O))],
v(T, O) = (openingQueriesM P u mac).eval (overlay (zeroDesig u T) O),
```

with `u = ofAffine input`, `mac = source.key.encode u`, `limbsOf v coins` the designated draws at
the true rows (`Glue.designatedLimbs`: the 182 free coordinates, the collector solve against the
free-filled rows of `v`, a uniform `sampleLane`-preimage of the designated vector),
`revealWeight … s = if revealOnPred … δ s then 0 else Ψ(P, L, s)`: **one** uniform oracle, read by
the opening through the zeroed tape (its value feeds the designated solve) and by the shadow's view
through the installed tape (the designated limbs are the drawn preimage's).
-/

import Proof.Privacy.Phase3.PublicFirst.LawsOnMerge

set_option linter.unusedSectionVars false
set_option maxRecDepth 8000
set_option autoImplicit false

namespace Kriterion.ArgoMAC.Security.Phase3.PublicFirst.OnLaw

open BN254 Cryptography GarbledCircuit Kriterion.ArgoMAC.PlanB
open Kriterion.ArgoMAC.Scheme (Coins Oracle)
open Kriterion.ArgoMAC.Security.OperationalOracle
open Kriterion.ArgoMAC.Phase3.Glue (Stage1Source publicCompletion openingQueriesM idealSamplers
  designatedLimbs programRequests DesignatedLimbs noRecord)
open Kriterion.ArgoMAC.Phase3.Lazy (LState Cell Tape Record Request queriesAlong uniformMaskTape
  runRefill cellOf)
open scoped ENNReal

noncomputable section

/-! ### 1. Generic sums -/

section Sums

theorem swapSum {α β : Type} (a : α → ℝ≥0∞) (b : β → ℝ≥0∞) (f : α → β → ℝ≥0∞) :
    ∑' x, a x * ∑' y, b y * f x y = ∑' y, b y * ∑' x, a x * f x y := by
  simp_rw [← ENNReal.tsum_mul_left]
  rw [ENNReal.tsum_comm]
  refine tsum_congr fun y => tsum_congr fun x => ?_
  ring

theorem elim_swap {β γ : Type} (r : Option β) (b : γ → ℝ≥0∞) (g : β → γ → ℝ≥0∞) :
    r.elim 0 (fun x => ∑' y, b y * g x y) = ∑' y, b y * r.elim 0 (fun x => g x y) := by
  cases r with
  | none => simp
  | some x => rfl

/-- Moving an inner average out of a coins–draws–offsets average. -/
theorem swap3 {C B D W : Type} (μ : C → ℝ≥0∞) (ν : C → Option B → ℝ≥0∞) (ρ : D → ℝ≥0∞)
    (w : W → ℝ≥0∞) (g : C → B → D → W → ℝ≥0∞) :
    ∑' c, μ c * ∑' r, ν c r * r.elim 0 (fun b => ∑' d, ρ d * ∑' o, w o * g c b d o) =
      ∑' o, w o * ∑' c, μ c * ∑' r, ν c r * r.elim 0 (fun b => ∑' d, ρ d * g c b d o) := by
  have inner : ∀ (c : C) (r : Option B), r.elim 0 (fun b => ∑' d, ρ d * ∑' o, w o * g c b d o) =
      ∑' o, w o * r.elim 0 (fun b => ∑' d, ρ d * g c b d o) := by
    intro c r
    rw [← elim_swap]
    congr 1
    funext b
    exact swapSum ρ w (g c b)
  simp_rw [inner]
  rw [← swapSum]
  refine tsum_congr fun c => congrArg _ ?_
  exact swapSum _ _ _

theorem elim_ite {S : Type} {c : Prop} (d : Decidable c) (s : S) (Φ : S → ℝ≥0∞) :
    (@ite _ c d none (some s)).elim 0 Φ = @ite _ c d 0 (Φ s) := by
  by_cases h : c
  · rw [if_pos h, if_pos h]
    rfl
  · rw [if_neg h, if_neg h]
    rfl

/-- A mapped run, read through `Option.elim`. -/
theorem map_weight {S : Type} (μ : PMF (Unit × S)) (g : Unit × S → Option S) (Φ W : S → ℝ≥0∞)
    (same : ∀ x, (g x).elim 0 Φ = W x.2) :
    ∑' o, (μ.map g) o * o.elim 0 Φ = ∑' x, μ x * W x.2 := by
  rw [tsum_map_mul]
  exact tsum_congr fun x => congrArg _ (same x)

theorem ite_congr_prop {c c' : Prop} (d : Decidable c) (d' : Decidable c') (h : c ↔ c') (a b : ℝ≥0∞) :
    @ite _ c d a b = @ite _ c' d' a b := by
  by_cases hc : c
  · rw [if_pos hc, if_pos (h.mp hc)]
  · rw [if_neg hc, if_neg fun h' => hc (h.mpr h')]

end Sums

/-! ### 2. Lookup invariance -/

section Invariance

variable [DecidableEq FixedIndex] [DecidableEq EncPRF.PermutationIndex]

theorem answerOf_congr {s t : LState} (same : SameLookups s t) : answerOf s = answerOf t := by
  funext q
  cases q <;> simp only [answerOf] <;> rw [same]

theorem padXor_congr {s t : LState} (same : SameLookups s t) : padXor s = padXor t := by
  funext coordinate position first
  simp only [padXor, lk, same.enc]

variable [FieldCertificate] [GroupCertificate]

theorem revealOnPred_congr (scalar : NonZeroScalar) (source : Stage1Source) (input : AffineInput)
    (coins : Coins) (delta : EncPRF.Coordinate → Block) {s t : LState} (same : SameLookups s t) :
    revealOnPred scalar source input coins delta s ↔ revealOnPred scalar source input coins delta t := by
  unfold revealOnPred prefixKeysOn
  rw [answerOf_congr same, padXor_congr same]

/-- **The reveal-flagged weight** of a private final state. -/
def revealWeight (scalar : NonZeroScalar) (source : Stage1Source) (input : AffineInput) (coins : Coins)
    (delta : EncPRF.Coordinate → Block) (Ψ : Public → LamportSignature → LState → ℝ≥0∞)
    (state : LState) : ℝ≥0∞ :=
  @ite _ (revealOnPred scalar source input coins delta state) (Classical.propDecidable _) 0
    (Ψ source.publicValue (sourceLabels source input) state)

theorem revealWeight_congr (scalar : NonZeroScalar) (source : Stage1Source) (input : AffineInput)
    (coins : Coins) (delta : EncPRF.Coordinate → Block) (Ψ : Public → LamportSignature → LState → ℝ≥0∞)
    (invariant : ∀ table labels first second, SameLookups first second →
      Ψ table labels first = Ψ table labels second)
    (s t : LState) (same : SameLookups s t) :
    revealWeight scalar source input coins delta Ψ s = revealWeight scalar source input coins delta Ψ t := by
  unfold revealWeight
  by_cases hit : revealOnPred scalar source input coins delta s
  · rw [if_pos hit, if_pos ((revealOnPred_congr scalar source input coins delta same).mp hit)]
  · rw [if_neg hit, if_neg (fun h => hit ((revealOnPred_congr scalar source input coins delta same).mpr h)),
      invariant _ _ _ _ same]

variable [Fintype FixedIndex] [Fintype EncPRF.PermutationIndex]

/-- A lazy run from two states with the same lookups has the same law, read through lookups. -/
theorem runLazyQ_weight_congr {α : Type} (c : FreeQuery Programs.Spec α) {s t : LState}
    (same : SameLookups s t) (W : LState → ℝ≥0∞) (invariant : ∀ u v, SameLookups u v → W u = W v) :
    ∑' x, runLazyQ c s x * W x.2 = ∑' x, runLazyQ c t x * W x.2 := by
  rw [runLazyQ_eager c s (fun _ u => W u) (fun _ u v h => invariant u v h),
    runLazyQ_eager c t (fun _ u => W u) (fun _ u v h => invariant u v h), publicCompletion_congr same]
  exact tsum_congr fun O => congrArg _ (invariant _ _ (plantAll_congr _ same))

end Invariance

/-! ### 3. The continuation after the opening -/

section Continuation

variable [FieldCertificate] [GroupCertificate] [Fintype FixedIndex] [Fintype EncPRF.PermutationIndex]
  [DecidableEq FixedIndex] [DecidableEq EncPRF.PermutationIndex]

theorem restore_source (source : Stage1Source) (input : AffineInput) :
    Lamport.restore input (sourceLabels source input) =
      ⟨BitInput.ofAffine input, source.key.encode (BitInput.ofAffine input)⟩ := by
  apply congrArg (Garbling.Labels.mk (BitInput.ofAffine input))
  apply InputMac.ext
  · apply Vector.ext
    intro index bound
    simp only [Lamport.selectedLabels, Vector.getElem_ofFn]
    rw [dif_pos (show index < 254 from bound)]
    rfl
  · apply Vector.ext
    intro index bound
    simp only [Lamport.selectedLabels, Vector.getElem_ofFn]
    rw [dif_neg (by omega)]
    simp only [Nat.add_sub_cancel_left]
    rfl

/-- The designated draws at the opening's value and the true rows of the coins. -/
def limbsOf (scalar : NonZeroScalar) (source : Stage1Source) (input : AffineInput)
    (value : (Fin pointElementCountX → BaseField) × (Fin pointElementCountY → BaseField)) (coins : Coins) :
    PMF (Option DesignatedLimbs) :=
  designatedLimbs idealSamplers source.publicValue (BitInput.ofAffine input) value.1 value.2
    (fun digit => trueRows scalar coins input digit)

/-- **The continuation after the opening**, as a weight. -/
def contW (scalar : NonZeroScalar) (source : Stage1Source) (input : AffineInput)
    (Ψ : Public → LamportSignature → LState → ℝ≥0∞)
    (ran : ((Fin pointElementCountX → BaseField) × (Fin pointElementCountY → BaseField)) × LState ×
      Record) : ℝ≥0∞ :=
  ∑' coins, PMF.uniformOfFintype Coins coins *
    ∑' r, limbsOf scalar source input ran.1 coins r *
      r.elim 0 fun limbs => ∑' delta, deltaLaw delta *
        ∑' x, runLazyQ (shadowOnM source.publicValue (BitInput.ofAffine input)
            (source.key.encode (BitInput.ofAffine input)))
          (Kriterion.ArgoMAC.Security.Phase3.programAllSkip
            (programRequests (BitInput.ofAffine input) ran.2.2 limbs) ran.2.1) x *
          revealWeight scalar source input coins delta Ψ x.2

theorem designedShadow_onCurve' (scalar : NonZeroScalar) (source : Stage1Source) (input : AffineInput)
    (coins : Coins) (coin : (designedShadow scalar).Coin)
    (ran : ((Fin pointElementCountX → BaseField) × (Fin pointElementCountY → BaseField)) × Record) :
    (designedShadow scalar).onCurve source input coins coin ran =
      shadowOnM source.publicValue (Lamport.restore input (sourceLabels source input)).input
        (Lamport.restore input (sourceLabels source input)).inputMac := rfl

/-- The offsets of a designed-shadow coin. -/
def coinDelta (scalar : NonZeroScalar) (coin : (designedShadow scalar).Coin) : EncPRF.Coordinate → Block :=
  coin.1

/-- The shadow's coin law, read at the offsets. -/
theorem designed_law_fst (scalar : NonZeroScalar) (g : (EncPRF.Coordinate → Block) → ℝ≥0∞) :
    ∑' coin, (designedShadow scalar).law coin * g (coinDelta scalar coin) =
      ∑' delta, deltaLaw delta * g delta := by
  show ∑' coin : (EncPRF.Coordinate → Block) × designedOff.Coin,
      (deltaLaw.bind fun delta => designedOff.law.map fun c => (delta, c)) coin * g coin.1 = _
  rw [tsum_bind_mul]
  refine tsum_congr fun delta => congrArg _ ?_
  rw [tsum_map_mul]
  dsimp only
  rw [ENNReal.tsum_mul_right, PMF.tsum_coe, one_mul]

/-- **`onCont`, read through the weight, is `contW`.** -/
theorem onCont_weight (scalar : NonZeroScalar) (source : Stage1Source) (input : AffineInput)
    (Ψ : Public → LamportSignature → LState → ℝ≥0∞)
    (ran : ((Fin pointElementCountX → BaseField) × (Fin pointElementCountY → BaseField)) × LState ×
      Record) :
    ∑' r, onCont scalar source input ran r *
        r.elim 0 (fun state => Ψ source.publicValue (sourceLabels source input) state) =
      contW scalar source input Ψ ran := by
  unfold onCont contW limbsOf
  rw [restore_source]
  dsimp only
  rw [tsum_bind_mul]
  refine tsum_congr fun coins => congrArg _ ?_
  rw [tsum_bind_mul]
  refine tsum_congr fun r => congrArg _ ?_
  rcases r with _ | limbs
  · dsimp only
    rw [tsum_pure_mul, Option.elim_none, Option.elim_none]
  · dsimp only
    rw [tsum_bind_mul]
    refine (tsum_congr fun coin => congrArg _ ?_).trans (designed_law_fst scalar (fun delta =>
      ∑' x, runLazyQ (shadowOnM source.publicValue (BitInput.ofAffine input)
          (source.key.encode (BitInput.ofAffine input)))
        (Kriterion.ArgoMAC.Security.Phase3.programAllSkip
          (programRequests (BitInput.ofAffine input) ran.2.2 limbs) ran.2.1) x *
        revealWeight scalar source input coins delta Ψ x.2))
    rw [designedShadow_onCurve', restore_source]
    dsimp only
    refine map_weight _ _ _ (revealWeight scalar source input coins (coinDelta scalar coin) Ψ) fun x => ?_
    rw [elim_ite]
    unfold revealWeight
    exact ite_congr_prop _ _ Iff.rfl _ _

/-- The continuation depends on the opening's state through its lookups only. -/
theorem contW_congr (scalar : NonZeroScalar) (source : Stage1Source) (input : AffineInput)
    (Ψ : Public → LamportSignature → LState → ℝ≥0∞)
    (invariant : ∀ table labels first second, SameLookups first second →
      Ψ table labels first = Ψ table labels second)
    (value : (Fin pointElementCountX → BaseField) × (Fin pointElementCountY → BaseField))
    (s t : LState) (record : Record) (same : SameLookups s t) :
    contW scalar source input Ψ (value, s, record) = contW scalar source input Ψ (value, t, record) := by
  unfold contW
  refine tsum_congr fun coins => congrArg _ (tsum_congr fun r => congrArg _ ?_)
  rcases r with _ | limbs
  · rw [Option.elim_none, Option.elim_none]
  · refine tsum_congr fun delta => congrArg _ ?_
    dsimp only
    rw [programAllSkip_eq, programAllSkip_eq]
    exact runLazyQ_weight_congr _ (plantAll_congr _ same) _
      (revealWeight_congr scalar source input coins delta Ψ invariant)

end Continuation

/-! ### 4. The private side, one oracle -/

section Private

variable [FieldCertificate] [GroupCertificate] [Fintype FixedIndex] [Fintype EncPRF.PermutationIndex]
  [DecidableEq FixedIndex] [DecidableEq EncPRF.PermutationIndex]

theorem transcript_eq_map {α : Type} (ans : ∀ q : PublicQuery FixedIndex EncPRF.PermutationIndex, q.Answer)
    (c : FreeQuery Programs.Spec α) :
    transcript ans c = (queriesAlong ans c).map fun q => (⟨q, ans q⟩ : Entry FixedIndex EncPRF.PermutationIndex) := by
  induction c with
  | pure value => rfl
  | query request next ih =>
      show ⟨request, ans request⟩ :: transcript ans (next (ans request)) =
        ⟨request, ans request⟩ :: (queriesAlong ans (next (ans request))).map _
      rw [ih]

/-- **The opening's non-limb transcript does not see the installed limbs.** -/
theorem filter_nonCell_install (bits : BitInput) (T : Tape) (limbs : DesignatedLimbs)
    (O : PublicOracle FixedIndex EncPRF.PermutationIndex) (table : Public) (mac : InputMac) :
    (transcript (publicAnswer (overlay (installTape bits T limbs) O)) (openingQueriesM table bits mac)).filter
        nonCell =
      (transcript (publicAnswer (overlay (zeroDesig bits T) O)) (openingQueriesM table bits mac)).filter
        nonCell := by
  have agree := agreeOff_install bits T limbs O
  have sameQ := pathSame_opening bits table mac _ _ agree
  have forward := cellOnce_forward (cellOnce_opening table bits mac)
  rw [transcript_eq_map, transcript_eq_map, ← sameQ, List.filter_map, List.filter_map]
  refine List.map_congr_left fun q member => ?_
  have inFilter := List.mem_filter.mp member
  have clear : Clear bits q := by
    refine ⟨?_, forward _ q inFilter.1⟩
    cases q with
    | hash key =>
        refine Kriterion.ArgoMAC.Phase3.Lazy.interceptAnswer_plain bits fun designated => ?_
        have keep := inFilter.2
        simp only [Function.comp] at keep
        have isNone : (cellOf key).isNone = true := keep
        exact cellOf_of_isDesignated bits designated (Option.isNone_iff_eq_none.mp isNone)
    | _ => rfl
  rw [agree q clear]

/-- **The merged kernel**: the coins, the designated draws at the opening's value, the
offsets, and the reveal-flagged weight at the view of the installed overlay of `O'`. -/
def mergeK (scalar : NonZeroScalar) (source : Stage1Source) (input : AffineInput)
    (Ψ : Public → LamportSignature → LState → ℝ≥0∞) (T : Tape)
    (value : (Fin pointElementCountX → BaseField) × (Fin pointElementCountY → BaseField))
    (O' : PublicOracle FixedIndex EncPRF.PermutationIndex) : ℝ≥0∞ :=
  ∑' coins, PMF.uniformOfFintype Coins coins *
    ∑' r, limbsOf scalar source input value coins r *
      r.elim 0 fun limbs => ∑' delta, deltaLaw delta *
        revealWeight scalar source input coins delta Ψ
          (onView source.publicValue (BitInput.ofAffine input) (source.key.encode (BitInput.ofAffine input))
            (overlay (installTape (BitInput.ofAffine input) T limbs) O'))

/-- **One oracle**: fixed the mask tape, the private continuation averaged over the opening's
oracle is the merged kernel at that same oracle. -/
theorem private_merge (scalar : NonZeroScalar) (source : Stage1Source) (input : AffineInput)
    (Ψ : Public → LamportSignature → LState → ℝ≥0∞)
    (invariant : ∀ table labels first second, SameLookups first second →
      Ψ table labels first = Ψ table labels second) (T : Tape) :
    ∑' O, PMF.uniformOfFintype (PublicOracle FixedIndex EncPRF.PermutationIndex) O *
        contW scalar source input Ψ
          (FreeQuery.eval (publicAnswer (overlay (zeroDesig (BitInput.ofAffine input) T) O))
            (openingQueriesM source.publicValue (BitInput.ofAffine input)
              (source.key.encode (BitInput.ofAffine input))),
          plantAll ((transcript (publicAnswer (overlay (zeroDesig (BitInput.ofAffine input) T) O))
            (openingQueriesM source.publicValue (BitInput.ofAffine input)
              (source.key.encode (BitInput.ofAffine input)))).filter (notDesig (BitInput.ofAffine input)))
            LazyOracle.empty,
          recordOf (BitInput.ofAffine input) (transcript (publicAnswer (overlay (zeroDesig
            (BitInput.ofAffine input) T) O)) (openingQueriesM source.publicValue (BitInput.ofAffine input)
              (source.key.encode (BitInput.ofAffine input)))) noRecord) =
      ∑' O, PMF.uniformOfFintype (PublicOracle FixedIndex EncPRF.PermutationIndex) O *
        mergeK scalar source input Ψ T
          (FreeQuery.eval (publicAnswer (overlay (zeroDesig (BitInput.ofAffine input) T) O))
            (openingQueriesM source.publicValue (BitInput.ofAffine input)
              (source.key.encode (BitInput.ofAffine input)))) O := by
  have forwardP : Hidden.QueryOnly NoInverse (openingQueriesM source.publicValue (BitInput.ofAffine input)
      (source.key.encode (BitInput.ofAffine input))) := cellOnce_queryOnly (cellOnce_opening _ _ _)
  have perO : ∀ O : PublicOracle FixedIndex EncPRF.PermutationIndex,
      contW scalar source input Ψ
          (FreeQuery.eval (publicAnswer (overlay (zeroDesig (BitInput.ofAffine input) T) O))
            (openingQueriesM source.publicValue (BitInput.ofAffine input)
              (source.key.encode (BitInput.ofAffine input))),
          plantAll ((transcript (publicAnswer (overlay (zeroDesig (BitInput.ofAffine input) T) O))
            (openingQueriesM source.publicValue (BitInput.ofAffine input)
              (source.key.encode (BitInput.ofAffine input)))).filter (notDesig (BitInput.ofAffine input)))
            LazyOracle.empty,
          recordOf (BitInput.ofAffine input) (transcript (publicAnswer (overlay (zeroDesig
            (BitInput.ofAffine input) T) O)) (openingQueriesM source.publicValue (BitInput.ofAffine input)
              (source.key.encode (BitInput.ofAffine input)))) noRecord) =
        ∑' O', publicCompletion (plantAll (Hidden.transcriptOf (publicAnswer O)
            (overlayProg (zeroDesig (BitInput.ofAffine input) T)
              (openingQueriesM source.publicValue (BitInput.ofAffine input)
                (source.key.encode (BitInput.ofAffine input))))) LazyOracle.empty) O' *
          mergeK scalar source input Ψ T
            (FreeQuery.eval (publicAnswer O) (overlayProg (zeroDesig (BitInput.ofAffine input) T)
              (openingQueriesM source.publicValue (BitInput.ofAffine input)
                (source.key.encode (BitInput.ofAffine input))))) O' := by
    intro O
    rw [(overlayProg_spec (zeroDesig (BitInput.ofAffine input) T) forwardP O).2]
    have inner : ∀ (coins : Coins) (limbs : DesignatedLimbs) (delta : EncPRF.Coordinate → Block),
        ∑' x, runLazyQ (shadowOnM source.publicValue (BitInput.ofAffine input)
            (source.key.encode (BitInput.ofAffine input)))
          (Kriterion.ArgoMAC.Security.Phase3.programAllSkip
            (programRequests (BitInput.ofAffine input) (recordOf (BitInput.ofAffine input)
              (transcript (publicAnswer (overlay (zeroDesig (BitInput.ofAffine input) T) O))
                (openingQueriesM source.publicValue (BitInput.ofAffine input)
                  (source.key.encode (BitInput.ofAffine input)))) noRecord) limbs)
            (plantAll ((transcript (publicAnswer (overlay (zeroDesig (BitInput.ofAffine input) T) O))
              (openingQueriesM source.publicValue (BitInput.ofAffine input)
                (source.key.encode (BitInput.ofAffine input)))).filter (notDesig (BitInput.ofAffine input)))
              LazyOracle.empty)) x *
          revealWeight scalar source input coins delta Ψ x.2 =
        ∑' O', publicCompletion (plantAll (Hidden.transcriptOf (publicAnswer O)
            (overlayProg (zeroDesig (BitInput.ofAffine input) T)
              (openingQueriesM source.publicValue (BitInput.ofAffine input)
                (source.key.encode (BitInput.ofAffine input))))) LazyOracle.empty) O' *
          revealWeight scalar source input coins delta Ψ
            (onView source.publicValue (BitInput.ofAffine input) (source.key.encode (BitInput.ofAffine input))
              (overlay (installTape (BitInput.ofAffine input) T limbs) O')) := by
      intro coins limbs delta
      refine (shadow_installed_eager source.publicValue (BitInput.ofAffine input)
        (source.key.encode (BitInput.ofAffine input)) (installTape (BitInput.ofAffine input) T limbs) O _
        (install_state (BitInput.ofAffine input) T O source.publicValue
          (source.key.encode (BitInput.ofAffine input)) limbs) _
        (revealWeight_congr scalar source input coins delta Ψ invariant)).trans
        ((completion_overlay_transcript (installTape (BitInput.ofAffine input) T limbs) O
          (openingQueriesM source.publicValue (BitInput.ofAffine input)
            (source.key.encode (BitInput.ofAffine input))) (cellOnce_opening _ _ _)
          (fun O'' => revealWeight scalar source input coins delta Ψ
            (onView source.publicValue (BitInput.ofAffine input)
              (source.key.encode (BitInput.ofAffine input)) O''))).trans ?_)
      rw [filter_nonCell_install, ← (overlayProg_spec (zeroDesig (BitInput.ofAffine input) T) forwardP O).1]
    unfold contW mergeK
    dsimp only
    simp only [inner]
    exact swap3 (fun coins => PMF.uniformOfFintype Coins coins)
      (fun coins r => limbsOf scalar source input
        (FreeQuery.eval (publicAnswer (overlay (zeroDesig (BitInput.ofAffine input) T) O))
          (openingQueriesM source.publicValue (BitInput.ofAffine input)
            (source.key.encode (BitInput.ofAffine input)))) coins r)
      deltaLaw
      (fun O' => publicCompletion (plantAll (Hidden.transcriptOf (publicAnswer O)
          (overlayProg (zeroDesig (BitInput.ofAffine input) T)
            (openingQueriesM source.publicValue (BitInput.ofAffine input)
              (source.key.encode (BitInput.ofAffine input))))) LazyOracle.empty) O')
      (fun coins limbs delta O' => revealWeight scalar source input coins delta Ψ
        (onView source.publicValue (BitInput.ofAffine input) (source.key.encode (BitInput.ofAffine input))
          (overlay (installTape (BitInput.ofAffine input) T limbs) O')))
  refine (tsum_congr fun O => congrArg _ (perO O)).trans ?_
  rw [merge_resample]
  refine tsum_congr fun O => congrArg _ ?_
  rw [(overlayProg_spec (zeroDesig (BitInput.ofAffine input) T) forwardP O).2]

/-- **(D) The private side of `LawOn`, per source.** -/
theorem private_source (scalar : NonZeroScalar) (source : Stage1Source) (input : AffineInput)
    (Ψ : Public → LamportSignature → LState → ℝ≥0∞)
    (invariant : ∀ table labels first second, SameLookups first second →
      Ψ table labels first = Ψ table labels second) :
    ∑' r, onPrivate scalar source input r *
        r.elim 0 (fun state => Ψ source.publicValue (sourceLabels source input) state) =
      ∑' T, uniformMaskTape T *
        ∑' O, PMF.uniformOfFintype (PublicOracle FixedIndex EncPRF.PermutationIndex) O *
          mergeK scalar source input Ψ T
            (FreeQuery.eval (publicAnswer (overlay (zeroDesig (BitInput.ofAffine input) T) O))
              (openingQueriesM source.publicValue (BitInput.ofAffine input)
                (source.key.encode (BitInput.ofAffine input)))) O := by
  unfold onPrivate
  rw [restore_source]
  dsimp only
  rw [tsum_bind_mul]
  refine tsum_congr fun T => congrArg _ ?_
  rw [tsum_bind_mul]
  refine (tsum_congr fun o => congrArg _ ?_).trans ((opening_eager (BitInput.ofAffine input) T
    source.publicValue (source.key.encode (BitInput.ofAffine input))
    (fun o => o.elim 0 (contW scalar source input Ψ))
    (fun a t t' r same => contW_congr scalar source input Ψ invariant a t t' r same)).trans
    (private_merge scalar source input Ψ invariant T))
  rcases o with _ | ran
  · dsimp only
    rw [tsum_pure_mul, Option.elim_none, Option.elim_none]
  · exact onCont_weight scalar source input Ψ ran

/-- **The private side's target form** (step D's result). -/
def onPrivForm (scalar : NonZeroScalar) (input : AffineInput)
    (Ψ : Public → LamportSignature → LState → ℝ≥0∞) : ℝ≥0∞ :=
  ∑' source, PMF.uniformOfFintype Stage1Source source *
    ∑' T, uniformMaskTape T *
      ∑' O, PMF.uniformOfFintype (PublicOracle FixedIndex EncPRF.PermutationIndex) O *
        mergeK scalar source input Ψ T
          (FreeQuery.eval (publicAnswer (overlay (zeroDesig (BitInput.ofAffine input) T) O))
            (openingQueriesM source.publicValue (BitInput.ofAffine input)
              (source.key.encode (BitInput.ofAffine input)))) O

/-- **(D) The private side of `LawOn` is `onPrivForm`.** -/
theorem lawOn_private (scalar : NonZeroScalar) (input : AffineInput)
    (Ψ : Public → LamportSignature → LState → ℝ≥0∞)
    (invariant : ∀ table labels first second, SameLookups first second →
      Ψ table labels first = Ψ table labels second) :
    ∑' source, PMF.uniformOfFintype Stage1Source source *
        ∑' r, onPrivate scalar source input r *
          (match r with
            | none => 0
            | some state => Ψ source.publicValue (sourceLabels source input) state) =
      onPrivForm scalar input Ψ := by
  unfold onPrivForm
  refine tsum_congr fun source => congrArg _ ?_
  refine Eq.trans (tsum_congr fun r => congrArg _ ?_) (private_source scalar source input Ψ invariant)
  rcases r with _ | state <;> rfl

end Private

end

end Kriterion.ArgoMAC.Security.Phase3.PublicFirst.OnLaw
