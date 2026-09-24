/-
**Phase 3, P1n — the off-curve law, step (iii): `LawOff`, as an equality.**

Both sides of `LawOff` are averages of one kernel (`offKernel`: the weight `Ψ` at a published
value, a MAC, and the lookups of the pads' transcript at `k₁` on EncPRF permutations `E` then of
system A's transcript on the view's fold answers `w` and view limbs `t`):

* the garbler's side (`rhs_table`, `rhs_split`): `swapped_reduce` (the garbler on an independent
  answer table), step (i) (`garbler_enc`, `garbler_designed`: the planted entries are the pads'
  transcript at the table's hash of the bridge input and system A's transcript), `systemAM_view`,
  then for fixed pads `tsum_maskTape_view` and `published_law` (`rhs_core`);
* the private side (`lhs_eq`): `designedOff_eager` (the pads on a uniform oracle, system A on
  uniform fixed-key answers and the limb tape), `systemAM_view`, `tsum_restrict`,
  `tsum_maskTape_view` and `tsum_source_cells`.

The two averages are the same, so `LawOff` holds with equality (`lawOff`).
-/

import Proof.Privacy.Phase3.PublicFirst.LawsOffView
import Proof.Privacy.Phase3.Lazy.FailAssembly

set_option linter.unusedSectionVars false
set_option maxRecDepth 8000
set_option autoImplicit false

namespace Kriterion.ArgoMAC.Security.Phase3.PublicFirst

open BN254 Cryptography GarbledCircuit Kriterion.ArgoMAC.PlanB Kriterion.ArgoMAC.FieldMacToECMac
open Kriterion.ArgoMAC.Scheme (Coins Oracle)
open Kriterion.ArgoMAC.Security.OperationalOracle
open Kriterion.ArgoMAC.Phase3.Lazy (Cell Tape LState uniformMaskTape)
open Kriterion.ArgoMAC.Phase3.Glue (Stage1Source publicCompletion)
open scoped ENNReal

noncomputable section

/- No `DecidableEq` or `Fintype` variables here: every average is read at the global instances
(those of `published_law`, `designedOff_eager`); `lawOff` transports the result to any instances. -/
variable [FieldCertificate] [GroupCertificate] (input : AffineInput)

/-- EncPRF answers from permutations. -/
def encAnswer (E : PermutationOracle EncPRF.PermutationIndex Block) :
    ∀ q : PublicQuery FixedIndex EncPRF.PermutationIndex, q.Answer :=
  tableAnswer (E, fun _ => (0, 0), fun _ => 0, fun _ => (0, 0))

/-- **The common kernel** of the two sides of `LawOff`. -/
def offKernel (Ψ : Public → LamportSignature → LState → ℝ≥0∞) (P : Public) (mac : InputMac)
    (k₁ : Block) (E : PermutationOracle EncPRF.PermutationIndex Block) (w : ViewIdx input → Block)
    (t : ViewSlot input → Block × Block) : ℝ≥0∞ :=
  Ψ P (Lamport.selectedLabels mac)
    (plantAll (transcript (fixedAnswer (extV input w) (replaceView input (fun _ => (0, 0)) t))
        (systemAM P (BitInput.ofAffine input) mac))
      (plantAll (transcript (encAnswer E) (Programs.padsM ⟨k₁, 0⟩)) LazyOracle.empty))

theorem pads_enc (ans : ∀ q : PublicQuery FixedIndex EncPRF.PermutationIndex, q.Answer)
    (E : PermutationOracle EncPRF.PermutationIndex Block)
    (same : ∀ i x, ans (.encForward i x) = E.permutation i x) (keys : WhiteningKeys) :
    transcript ans (Programs.padsM keys) = transcript (encAnswer E) (Programs.padsM keys) := by
  refine transcript_agree_on (Hidden.padsM_encOnly keys) _ _ fun q enc => ?_
  cases q with
  | encForward i x => exact same i x
  | _ => exact enc.elim

theorem system_fixed (A : Table) (P : Public) (mac : InputMac) :
    transcript (tableAnswer A) (systemAM P (BitInput.ofAffine input) mac) =
      transcript (fixedAnswer A.2.2.1 A.2.2.2) (systemAM P (BitInput.ofAffine input) mac) := by
  refine transcript_agree_on (systemAM_only input P mac) _ _ fun q view => ?_
  cases q with
  | fixedForward i x => rfl
  | hash key =>
      obtain ⟨cell, label, -, rfl⟩ := view
      rw [fixedAnswer, tableAnswer_cell, tableAnswer_cell]
  | _ => exact view.elim

/-- The pads of permutations and a hash value. -/
def padsOf (E : PermutationOracle EncPRF.PermutationIndex Block) (h : Block × Block) :
    Programs.Pads :=
  (Programs.padsM ⟨h.1, h.2⟩).eval (encAnswer E)

/-- The bridge input of a bridge key, off the scale range. -/
def bridgeOther (t : BaseField) : OtherInput := ⟨bridgeInput t, bridgeInput_not_lt t⟩

theorem tableHash_bridge (A : Table) (t : BaseField) :
    tableHash A (bridgeInput t) = A.2.1 (bridgeOther t) :=
  tableAnswer_other A (bridgeOther t)

theorem tablePads_eq (A : Table) (coins : Coins) :
    tablePads A coins = padsOf A.1 (tableHash A (bridgeInput coins.bridgeKey)) :=
  eval_agree (Hidden.padsM_encOnly _) _ _ fun q enc => by
    cases q with
    | encForward i x => rfl
    | _ => exact enc.elim

variable (parameter : ℕ) (scalar : NonZeroScalar)

/-- **The garbler's side, on a table.** -/
theorem rhs_table (invalid : validate input = false)
    (Ψ : Public → LamportSignature → LState → ℝ≥0∞) :
    ∑' tape, swappedChallengeTape tape *
        Ψ (Scheme.scheme.garble parameter scalar tape).1
          (Scheme.scheme.encode (Scheme.scheme.garble parameter scalar tape).2 input)
          (plantAll (upperEntries parameter scalar tape input) LazyOracle.empty) =
      ∑' coins, PMF.uniformOfFintype Coins coins * ∑' A, tableLaw A *
        offKernel input Ψ
          (tablePub scalar coins (padsOf A.1 (A.2.1 (bridgeOther coins.bridgeKey))) A.2.2.1 A.2.2.2)
          (coins.inputMacKey.encode (BitInput.ofAffine input))
          (A.2.1 (bridgeOther coins.bridgeKey)).1 A.1 (A.2.2.1 ∘ viewIdx input)
          (viewCells input A.2.2.2) := by
  let O₀ : Oracle := Classical.arbitrary _
  let G : Coins → List (Entry FixedIndex EncPRF.PermutationIndex) → Public × InputMacKey → ℝ≥0∞ :=
    fun coins trans R => Ψ R.1 (Scheme.scheme.encode R.2 input)
      (plantAll (trans.filter Entry.IsEnc ++ trans.filter (designedKeep scalar (coins, O₀) input))
        LazyOracle.empty)
  have pointwise : ∀ tape : Coins × Oracle,
      Ψ (Scheme.scheme.garble parameter scalar tape).1
          (Scheme.scheme.encode (Scheme.scheme.garble parameter scalar tape).2 input)
          (plantAll (upperEntries parameter scalar tape input) LazyOracle.empty) =
        G tape.1 (garblerTranscript scalar tape)
          ((Programs.garbleM scalar tape.1).eval (publicAnswer tape.2)) := by
    intro tape
    rw [← garble_eval parameter scalar tape.1 tape.2]
    rfl
  rw [tsum_congr fun tape => congrArg _ (pointwise tape), swapped_reduce scalar G]
  refine tsum_congr fun coins => congrArg _ (tsum_congr fun A => congrArg _ ?_)
  have designed := garbler_designed scalar (coins, O₀) input A coins invalid
  have enc := garbler_enc (tableAnswer A) scalar coins
  have first := garbleM_tablePub scalar A coins
  have second : ((Programs.garbleM scalar coins).eval (tableAnswer A)).2 = coins.inputMacKey := by
    rw [garbleM_table]
  have hashEq : (Programs.askHash (bridgeInput coins.bridgeKey)).eval (tableAnswer A) =
      A.2.1 (bridgeOther coins.bridgeKey) :=
    (eval_askHash_ans (tableAnswer A) _).trans (tableHash_bridge A coins.bridgeKey)
  show Ψ _ _ (plantAll (_ ++ _) _) = _
  rw [designed, enc, first, second, tablePads_eq, tableHash_bridge, hashEq]
  unfold plantAll
  rw [List.foldl_append, system_fixed, systemAM_view,
    pads_enc (tableAnswer A) A.1 (fun _ _ => rfl)]
  rfl

/-- **The garbler's side for fixed pads**: the published law. -/
theorem rhs_core (Ψ : Public → LamportSignature → LState → ℝ≥0∞) (pads : Programs.Pads)
    (k₁ : Block) (E : PermutationOracle EncPRF.PermutationIndex Block) :
    ∑' coins, PMF.uniformOfFintype Coins coins *
      ∑' v, PMF.uniformOfFintype (FixedIndex → Block) v *
        ∑' T, uniformMaskTape T * offKernel input Ψ (tablePub scalar coins pads v T)
          (coins.inputMacKey.encode (BitInput.ofAffine input)) k₁ E (v ∘ viewIdx input)
          (viewCells input T) =
    ∑' cells, PMF.uniformOfFintype PublicCells cells *
      ∑' vis, PMF.uniformOfFintype (CurveVisible (offShape input)) vis *
        ∑' key, PMF.uniformOfFintype InputMacKey key *
          ∑' w, PMF.uniformOfFintype (ViewIdx input → Block) w *
            ∑' t, fibreLaw (masksOf (viewLane input)) (masksOf_surjective _) (visEquiv input vis)
                t *
              offKernel input Ψ (cellsSource cells defaultKey).publicValue
                (key.encode (BitInput.ofAffine input)) k₁ E w t := by
  have cells : ∀ coins v T, tablePub scalar coins pads v T =
      pubOf scalar input pads coins v (masksOf VectorSite.lane T) :=
    fun coins v T => tablePub_cells scalar input pads coins v T defaultKey _ rfl
  have perCoins : ∀ coins v, ∑' T, uniformMaskTape T *
      offKernel input Ψ (tablePub scalar coins pads v T)
        (coins.inputMacKey.encode (BitInput.ofAffine input)) k₁ E (v ∘ viewIdx input)
        (viewCells input T) =
      ∑' m, PMF.uniformOfFintype MaskVectors m *
        (fun P mac w vis => ∑' t, fibreLaw (masksOf (viewLane input)) (masksOf_surjective _)
          (visEquiv input vis) t * offKernel input Ψ P mac k₁ E w t)
          (pubOf scalar input pads coins v m) (coins.inputMacKey.encode (BitInput.ofAffine input))
          (v ∘ viewIdx input)
          (curveVisible (offShape input) (maskSiteEquiv (maskCoordEquiv m)).2) := by
    intro coins v
    simp only [cells]
    exact (tsum_maskTape_view input (fun m t => offKernel input Ψ
      (pubOf scalar input pads coins v m) (coins.inputMacKey.encode (BitInput.ofAffine input)) k₁ E
      (v ∘ viewIdx input) t)).trans
      (tsum_congr fun m => by rw [viewMasks_eq])
  rw [tsum_congr fun coins => congrArg _ (tsum_congr fun v => congrArg _ (perCoins coins v))]
  exact published_law scalar input pads (fun P mac w vis => ∑' t,
    fibreLaw (masksOf (viewLane input)) (masksOf_surjective _) (visEquiv input vis) t *
      offKernel input Ψ P mac k₁ E w t)

/-- The common average of the two sides, at `k₁` and `E`. -/
def offCore (Ψ : Public → LamportSignature → LState → ℝ≥0∞) (k₁ : Block)
    (E : PermutationOracle EncPRF.PermutationIndex Block) : ℝ≥0∞ :=
  ∑' cells, PMF.uniformOfFintype PublicCells cells *
    ∑' vis, PMF.uniformOfFintype (CurveVisible (offShape input)) vis *
      ∑' key, PMF.uniformOfFintype InputMacKey key *
        ∑' w, PMF.uniformOfFintype (ViewIdx input → Block) w *
          ∑' t, fibreLaw (masksOf (viewLane input)) (masksOf_surjective _) (visEquiv input vis) t *
            offKernel input Ψ (cellsSource cells defaultKey).publicValue
              (key.encode (BitInput.ofAffine input)) k₁ E w t

/-- **The garbler's side is the common average.** -/
theorem rhs_split (Ψ : Public → LamportSignature → LState → ℝ≥0∞) :
    ∑' coins, PMF.uniformOfFintype Coins coins * ∑' A, tableLaw A *
        offKernel input Ψ
          (tablePub scalar coins (padsOf A.1 (A.2.1 (bridgeOther coins.bridgeKey))) A.2.2.1 A.2.2.2)
          (coins.inputMacKey.encode (BitInput.ofAffine input))
          (A.2.1 (bridgeOther coins.bridgeKey)).1 A.1 (A.2.2.1 ∘ viewIdx input)
          (viewCells input A.2.2.2) =
      ∑' E, PMF.uniformOfFintype (PermutationOracle EncPRF.PermutationIndex Block) E *
        ∑' k₁, PMF.uniformOfFintype Block k₁ * offCore input Ψ k₁ E := by
  have hashAvg : ∀ (key : OtherInput) (g : Block × Block → ℝ≥0∞),
      ∑' H, PMF.uniformOfFintype OtherTable H * g (H key) =
        ∑' h, PMF.uniformOfFintype (Block × Block) h * g h := by
    intro key g
    refine (tsum_uniform_split key id (fun c (_ : OtherTable) => g c) fun _ _ _ => rfl).trans ?_
    rw [PMF.map_id]
    exact tsum_congr fun h => congrArg _ (tsum_const_uniform _)
  let X : Coins → PermutationOracle EncPRF.PermutationIndex Block → Block × Block → ℝ≥0∞ :=
    fun coins E h => ∑' v, PMF.uniformOfFintype (FixedIndex → Block) v * ∑' T, uniformMaskTape T *
      offKernel input Ψ (tablePub scalar coins (padsOf E h) v T)
        (coins.inputMacKey.encode (BitInput.ofAffine input)) h.1 E (v ∘ viewIdx input)
        (viewCells input T)
  have expand : ∀ coins, ∑' A, tableLaw A *
      offKernel input Ψ
        (tablePub scalar coins (padsOf A.1 (A.2.1 (bridgeOther coins.bridgeKey))) A.2.2.1 A.2.2.2)
        (coins.inputMacKey.encode (BitInput.ofAffine input))
        (A.2.1 (bridgeOther coins.bridgeKey)).1 A.1 (A.2.2.1 ∘ viewIdx input)
        (viewCells input A.2.2.2) =
      ∑' E, PMF.uniformOfFintype (PermutationOracle EncPRF.PermutationIndex Block) E *
        ∑' h, PMF.uniformOfFintype (Block × Block) h * X coins E h := by
    intro coins
    unfold tableLaw
    rw [tsum_productPMF]
    refine tsum_congr fun E => congrArg _ ?_
    rw [tsum_productPMF]
    refine (tsum_congr fun H => congrArg _ ?_).trans
      (hashAvg (bridgeOther coins.bridgeKey) (X coins E))
    rw [tsum_productPMF]
  simp only [expand]
  rw [tsum_swap_mul]
  refine tsum_congr fun E => congrArg _ ?_
  rw [tsum_swap_mul, tsum_uniform_prod]
  refine tsum_congr fun k₁ => congrArg _ ?_
  have core : ∀ k₂, ∑' coins, PMF.uniformOfFintype Coins coins * X coins E (k₁, k₂) =
      offCore input Ψ k₁ E := fun k₂ => rhs_core input scalar Ψ (padsOf E (k₁, k₂)) k₁ E
  simp only [core]
  exact tsum_const_uniform _

/-! ### The private side -/

/-- **The private run at a coin and a tape**, eager: the pads on uniform EncPRF permutations, system
A on uniform view answers. -/
theorem lhs_inner (Ψ : Public → LamportSignature → LState → ℝ≥0∞)
    (invariant : ∀ table labels first second, SameLookups first second →
      Ψ table labels first = Ψ table labels second)
    (source : Stage1Source) (k₁ : Block) (T : Tape) (M : Option (Unit × LState) → ℝ≥0∞)
    (none' : M none = 0)
    (some' : ∀ x, M (some x) = Ψ source.publicValue (sourceLabels source input) x.2)
    (bits : BitInput) (bitsEq : bits = BitInput.ofAffine input)
    (mac : InputMac) (macEq : mac = source.key.encode (BitInput.ofAffine input)) :
    ∑' r, runFillFlag LazyOracle.empty (fun cell => PMF.pure (T cell))
        (designedOffM source.publicValue bits mac k₁) LazyOracle.empty ∅ r * M r =
      ∑' E, PMF.uniformOfFintype (PermutationOracle EncPRF.PermutationIndex Block) E *
        ∑' w, PMF.uniformOfFintype (ViewIdx input → Block) w *
          offKernel input Ψ source.publicValue (source.key.encode (BitInput.ofAffine input)) k₁ E w
            (viewCells input T) := by
  subst bitsEq macEq
  have weight : ∀ r, M r = (match r with
      | none => 0
      | some x => Ψ source.publicValue (sourceLabels source input) x.2) := by
    rintro (_ | x)
    · exact none'
    · exact some' x
  rw [tsum_congr fun r => congrArg _ (weight r)]
  refine (designedOff_eager source.publicValue (BitInput.ofAffine input)
    (source.key.encode (BitInput.ofAffine input)) k₁ T
    (Ψ source.publicValue (sourceLabels source input)) (invariant _ _)).trans ?_
  rw [Kriterion.ArgoMAC.Phase3.Glue.public_initial]
  have pointwise : ∀ O : PublicOracle FixedIndex EncPRF.PermutationIndex,
      ∑' v, PMF.uniformOfFintype (FixedIndex → Block) v *
        Ψ source.publicValue (sourceLabels source input)
          (plantAll (transcript (fixedAnswer v T) (systemAM source.publicValue
            (BitInput.ofAffine input) (source.key.encode (BitInput.ofAffine input))))
            (plantAll (transcript (publicAnswer O) (Programs.padsM ⟨k₁, 0⟩)) LazyOracle.empty)) =
      ∑' w, PMF.uniformOfFintype (ViewIdx input → Block) w *
        offKernel input Ψ source.publicValue (source.key.encode (BitInput.ofAffine input)) k₁ O.2.1
          w (viewCells input T) := by
    intro O
    rw [pads_enc (publicAnswer O) O.2.1 (fun _ _ => rfl)]
    have view : ∀ v : FixedIndex → Block, transcript (fixedAnswer v T) (systemAM source.publicValue
        (BitInput.ofAffine input) (source.key.encode (BitInput.ofAffine input))) =
        transcript (fixedAnswer (extV input (v ∘ viewIdx input))
          (replaceView input (fun _ => (0, 0)) (viewCells input T)))
          (systemAM source.publicValue (BitInput.ofAffine input)
            (source.key.encode (BitInput.ofAffine input))) := fun v => systemAM_view input _ _ v T
    rw [tsum_congr fun v => by rw [view v]]
    exact tsum_restrict (viewIdx input) (viewIdx_injective input) (fun w => offKernel input Ψ
      source.publicValue (source.key.encode (BitInput.ofAffine input)) k₁ O.2.1 w
        (viewCells input T))
  rw [tsum_congr fun O => congrArg _ (pointwise O), tsum_uniform_prod]
  dsimp only
  rw [tsum_const_uniform, tsum_uniform_prod]
  dsimp only
  refine tsum_congr fun E => congrArg _ ?_
  exact tsum_const_uniform _

/-- **The mask tape at the view**: uniform visible masks and their view vectors' fibre. -/
theorem lhs_tape (g : (ViewSlot input → Block × Block) → ℝ≥0∞) :
    ∑' T, uniformMaskTape T * g (viewCells input T) =
      ∑' vis, PMF.uniformOfFintype (CurveVisible (offShape input)) vis *
        ∑' t, fibreLaw (masksOf (viewLane input)) (masksOf_surjective _) (visEquiv input vis) t *
          g t := by
  have push := tsum_map_mul (PMF.uniformOfFintype MaskVectors) (viewMasks input)
    (fun μ => ∑' t, fibreLaw (masksOf (viewLane input)) (masksOf_surjective _) μ t * g t)
  rw [viewMasks_uniform] at push
  refine (tsum_maskTape_view input (fun _ t => g t)).trans (push.symm.trans ?_)
  rw [tsum_equiv_uniform (visEquiv input).symm]
  rfl

/-- The private side's weight of an outcome. -/
def offWeightΨ (Ψ : Public → LamportSignature → LState → ℝ≥0∞) (source : Stage1Source)
    (r : Option (Unit × LState)) : ℝ≥0∞ :=
  Option.elim r 0 fun x => Ψ source.publicValue (sourceLabels source input) x.2

/-- **The private side is the common average.** -/
theorem lhs_eq (Ψ : Public → LamportSignature → LState → ℝ≥0∞)
    (invariant : ∀ table labels first second, SameLookups first second →
      Ψ table labels first = Ψ table labels second) :
    ∑' source, PMF.uniformOfFintype Stage1Source source *
        ∑' r, offPrivate scalar source input r * offWeightΨ input Ψ source r =
      ∑' E, PMF.uniformOfFintype (PermutationOracle EncPRF.PermutationIndex Block) E *
        ∑' k₁, PMF.uniformOfFintype Block k₁ * offCore input Ψ k₁ E := by
  have perSource : ∀ source : Stage1Source, ∑' r, offPrivate scalar source input r *
      offWeightΨ input Ψ source r =
      ∑' k₁, PMF.uniformOfFintype Block k₁ *
        ∑' vis, PMF.uniformOfFintype (CurveVisible (offShape input)) vis *
          ∑' t, fibreLaw (masksOf (viewLane input)) (masksOf_surjective _) (visEquiv input vis) t *
            ∑' E, PMF.uniformOfFintype (PermutationOracle EncPRF.PermutationIndex Block) E *
              ∑' w, PMF.uniformOfFintype (ViewIdx input → Block) w *
                offKernel input Ψ source.publicValue (source.key.encode (BitInput.ofAffine input))
                  k₁ E w t := by
    intro source
    have restoreEq : Lamport.restore input (sourceLabels source input) =
        ⟨BitInput.ofAffine input, source.key.encode (BitInput.ofAffine input)⟩ :=
      Kriterion.ArgoMAC.Phase3.Lazy.restore_selectedLabels input _
    unfold offPrivate
    rw [tsum_bind_mul]
    have inner : ∀ coin : (designedShadow scalar).Coin, ∑' r, (uniformMaskTape.bind fun T =>
        runFillFlag LazyOracle.empty (fun cell => PMF.pure (T cell))
          ((designedShadow scalar).offCurve source input coin) LazyOracle.empty ∅) r *
        offWeightΨ input Ψ source r =
        ∑' vis, PMF.uniformOfFintype (CurveVisible (offShape input)) vis *
          ∑' t, fibreLaw (masksOf (viewLane input)) (masksOf_surjective _) (visEquiv input vis) t *
            ∑' E, PMF.uniformOfFintype (PermutationOracle EncPRF.PermutationIndex Block) E *
              ∑' w, PMF.uniformOfFintype (ViewIdx input → Block) w *
                offKernel input Ψ source.publicValue (source.key.encode (BitInput.ofAffine input))
                  coin.2 E w t := by
      intro coin
      rw [tsum_bind_mul, designedShadow_offCurve, restoreEq]
      rw [tsum_congr fun T => congrArg (uniformMaskTape T * ·) (lhs_inner input Ψ invariant source
        coin.2 T (offWeightΨ input Ψ source) rfl (fun _ => rfl) _ rfl _ rfl)]
      exact (lhs_tape input fun t =>
          ∑' E, PMF.uniformOfFintype (PermutationOracle EncPRF.PermutationIndex Block) E *
            ∑' w, PMF.uniformOfFintype (ViewIdx input → Block) w *
              offKernel input Ψ source.publicValue (source.key.encode (BitInput.ofAffine input))
                coin.2 E w t)
    rw [tsum_congr fun coin => congrArg ((designedShadow scalar).law coin * ·) (inner coin)]
    change ∑' coin, productPMF deltaLaw (PMF.uniformOfFintype Block) coin * _ = _
    rw [tsum_productPMF]
    unfold deltaLaw
    dsimp only
    exact tsum_const_uniform _
  have publicKey : ∀ (cells : PublicCells) (key : InputMacKey),
      (cellsSource cells key).publicValue = (cellsSource cells defaultKey).publicValue :=
    fun _ _ => rfl
  have keyKey : ∀ (cells : PublicCells) (key : InputMacKey), (cellsSource cells key).key = key :=
    fun _ _ => rfl
  have swapB : ∀ {α : Type} (μ : α → ℝ≥0∞) (f : α → Block → ℝ≥0∞),
      ∑' a, μ a * ∑' b, PMF.uniformOfFintype Block b * f a b =
        ∑' b, PMF.uniformOfFintype Block b * ∑' a, μ a * f a b := fun μ f => tsum_swap_mul μ _ f
  have swapE : ∀ {α : Type} (μ : α → ℝ≥0∞)
      (f : α → PermutationOracle EncPRF.PermutationIndex Block → ℝ≥0∞),
      ∑' a, μ a * ∑' b, PMF.uniformOfFintype (PermutationOracle EncPRF.PermutationIndex Block) b *
          f a b =
        ∑' b, PMF.uniformOfFintype (PermutationOracle EncPRF.PermutationIndex Block) b *
          ∑' a, μ a * f a b := fun μ f => tsum_swap_mul μ _ f
  have swapW : ∀ (vis : CurveVisible (offShape input))
      (f : (ViewSlot input → Block × Block) → (ViewIdx input → Block) → ℝ≥0∞),
      ∑' a, fibreLaw (masksOf (viewLane input)) (masksOf_surjective _) (visEquiv input vis) a *
          ∑' b, PMF.uniformOfFintype (ViewIdx input → Block) b * f a b =
        ∑' b, PMF.uniformOfFintype (ViewIdx input → Block) b *
          ∑' a, fibreLaw (masksOf (viewLane input)) (masksOf_surjective _) (visEquiv input vis) a *
            f a b :=
    fun vis f => tsum_swap_mul _ _ f
  have swapKV : ∀ (f : InputMacKey → CurveVisible (offShape input) → ℝ≥0∞),
      ∑' a, PMF.uniformOfFintype InputMacKey a *
          ∑' b, PMF.uniformOfFintype (CurveVisible (offShape input)) b * f a b =
        ∑' b, PMF.uniformOfFintype (CurveVisible (offShape input)) b *
          ∑' a, PMF.uniformOfFintype InputMacKey a * f a b := fun f => tsum_swap_mul _ _ f
  rw [tsum_congr fun source => congrArg _ (perSource source), tsum_source_cells]
  simp only [publicKey, keyKey]
  simp only [swapB]
  simp only [swapE]
  simp only [swapW]
  simp only [swapKV]
  rfl

/-- The private side at any weight that is `offWeightΨ` pointwise. -/
theorem lhs_eq' (Ψ : Public → LamportSignature → LState → ℝ≥0∞)
    (invariant : ∀ table labels first second, SameLookups first second →
      Ψ table labels first = Ψ table labels second)
    (M : Stage1Source → Option (Unit × LState) → ℝ≥0∞) (none' : ∀ source, M source none = 0)
    (some' : ∀ source x, M source (some x) = Ψ source.publicValue (sourceLabels source input) x.2) :
    ∑' source, PMF.uniformOfFintype Stage1Source source *
        ∑' r, offPrivate scalar source input r * M source r =
      ∑' E, PMF.uniformOfFintype (PermutationOracle EncPRF.PermutationIndex Block) E *
        ∑' k₁, PMF.uniformOfFintype Block k₁ * offCore input Ψ k₁ E := by
  have weight : ∀ source r, M source r = offWeightΨ input Ψ source r := by
    intro source r
    cases r with
    | none => exact none' source
    | some x => exact some' source x
  simp only [weight]
  exact lhs_eq input scalar Ψ invariant

/-! ### `LawOff` -/

theorem validate_of_off (input : AffineInput) (off : Scheme.scheme.function scalar input = none) :
    validate input = false := by
  have decoded : decodePoint input = none := Option.map_eq_none_iff.mp off
  cases valid : validate input
  · rfl
  · exfalso
    simp [decodePoint, valid] at decoded

/-- **`LawOff` holds, with equality** (at any instances). -/
theorem lawOff_global (off : Scheme.scheme.function scalar input = none) :
    LawOff parameter scalar input := by
  intro Ψ invariant
  have invalid := validate_of_off scalar input off
  have right :=
    (rhs_split input scalar Ψ).symm.trans (rhs_table input parameter scalar invalid Ψ).symm
  refine le_of_eq ?_
  refine Eq.trans ?_ right
  exact lhs_eq' input scalar Ψ invariant _ (fun _ => rfl) (fun _ _ => rfl)

/-- **`LawOff` holds, with equality**, at any `DecidableEq` instances (they are subsingletons). -/
theorem lawOff (off : Scheme.scheme.function scalar input = none)
    [first : DecidableEq FixedIndex] [second : DecidableEq EncPRF.PermutationIndex] :
    LawOff parameter scalar input := by
  have global := lawOff_global input parameter scalar off
  convert global using 1

/-- **`LawOff` at every off-curve input**, as `LiftOn.designedLift_of_laws` takes it. -/
theorem lawOff_all [first : DecidableEq FixedIndex] [second : DecidableEq EncPRF.PermutationIndex] :
    ∀ input, Scheme.scheme.function scalar input = none → LawOff parameter scalar input :=
  fun input off => lawOff input parameter scalar off

end

end Kriterion.ArgoMAC.Security.Phase3.PublicFirst
