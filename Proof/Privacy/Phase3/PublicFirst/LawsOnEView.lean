/-
**Phase 3, P1r — `LawOn`, step (E), part 2: the on-curve shadow reads only its view.**

At a fixed input `u` the on-curve shadow (`shadowOnM`: the prefix, the bit-`true` pads, the whole
evaluator) asks, whatever the answers (`shadow_onQ`, index-based):

* at every (lane, chunk) of the **four** lanes and every paid fold step `0 < n < b_c`, both halves of
  every gate off the step's active parent (`ViewIdx`, `activeEntry`);
* every gadget position of every digit;
* the limbs of the inactive vector sites (`Inact`, `ICell`), at any label, and the hash off the scale
  range (the bridge);
* EncPRF questions.

So on answer tables the shadow's transcript reads a table only through its EncPRF permutations, its
hash off the scale range, its fixed-key answers at the view indices (`VO`) and its limbs at the
inactive vector sites (`transcript_view`), and the kernel of `LawOn`'s both sides, `onK` (the weight
at a published value, a key's selected labels and the shadow's planted transcript on a table), is a
function `onKV` of exactly these (`onK_view`).
-/

import Proof.Privacy.Phase3.PublicFirst.LawsOnEEval

set_option linter.unusedSectionVars false
set_option maxRecDepth 8000
set_option autoImplicit false

namespace Kriterion.ArgoMAC.Security.Phase3.PublicFirst.OnE

open BN254 Cryptography GarbledCircuit Kriterion.ArgoMAC.PlanB
open Kriterion.ArgoMAC.Scheme (Coins Oracle)
open Kriterion.ArgoMAC.Security.OperationalOracle
open Kriterion.ArgoMAC.Phase3.Lazy (Cell Tape LState cellOf cellInput)
open scoped ENNReal

noncomputable section

/-- Two answer functions agreeing on a program's questions give it the same transcript. -/
theorem transcript_agree_only {α : Type} {S : PublicQuery FixedIndex EncPRF.PermutationIndex → Prop}
    {c : FreeQuery Programs.Spec α} (only : Hidden.QueryOnly S c)
    (a b : ∀ q : PublicQuery FixedIndex EncPRF.PermutationIndex, q.Answer)
    (same : ∀ q, S q → a q = b q) : transcript a c = transcript b c := by
  induction only with
  | pure value => rfl
  | query request next holds rest ih =>
      show ⟨request, a request⟩ :: transcript a (next (a request)) =
        ⟨request, b request⟩ :: transcript b (next (b request))
      rw [ih (a request), same request holds]

variable [FieldCertificate] [GroupCertificate] (input : AffineInput)

/-! ### 1. The view's indices -/

/-- **An inactive vector site**: its switch is not the active one of its chunk at `u`. -/
def Inact (s : VectorSite) : Prop :=
  s.switch ≠ chunkOf (Pipeline.coordBits (BitInput.ofAffine input) s.lane.coord) s.chunk

instance (s : VectorSite) : Decidable (Inact input s) := by unfold Inact; infer_instance

/-- The limbs of the inactive vector sites. -/
abbrev ICell := {c : Cell // Inact input c.1}

/-- The active parent's entry at a fold step of a (lane, chunk), at `u`. -/
def activeEntry (lane : Lane) (c : Fin chunkCount) (fold : Nat) : Nat :=
  (chunkValue (Pipeline.coordBits (BitInput.ofAffine input) lane.coord) c).toNat % 2 ^ fold

/-- **A view index**: a fold gate the evaluator asks at `u` (a paid step of its chunk, an entry off
the step's active parent, either half), or a gadget position. -/
def ViewIdx : FixedIndex → Prop
  | .hot lane c fold entry _ => 0 < fold.val ∧ fold.val < chunkWidth c ∧ entry.val < 2 ^ fold.val ∧
      entry.val ≠ activeEntry input lane c fold.val
  | .gadget _ _ _ => True

/-- **The view's fixed-key indices.** -/
abbrev VO := {i : FixedIndex // ViewIdx input i}

noncomputable instance voFintype : Fintype (VO input) := Fintype.ofFinite _

/-! ### 2. The shadow's questions -/

/-- A hash key the view reads: a limb of an inactive vector site (any label), or off the scale
range. (Irreducible: unfolding it would make Lean decide `cellOf`'s existential.) -/
@[irreducible] def HashView (key : BaseField) : Prop :=
  (cellOf key).elim (¬ key.val < scaleRange) fun cell => Inact input cell.1

/-- **A view question**: a fixed-key question at a view index (any input), an EncPRF forward
question, a hash question the view reads. -/
def OnQ : PublicQuery FixedIndex EncPRF.PermutationIndex → Prop
  | .fixedForward index _ => ViewIdx input index
  | .encForward _ _ => True
  | .hash key => HashView input key
  | _ => False

theorem onQ_hot (lane : Lane) (c : Fin chunkCount) (n e : Nat) (half : Bool) (x : Block)
    (paid : 0 < n) (small : n < chunkWidth c) (entry : e < 2 ^ n) (off : e ≠ activeEntry input lane c n) :
    OnQ input (.fixedForward (hotIndexNat lane c n e half) x) := by
  have le := chunkWidth_le c
  have foldEq : n % chunkBits = n := Nat.mod_eq_of_lt (by omega)
  have entryEq : e % 2 ^ chunkBits = e :=
    Nat.mod_eq_of_lt (lt_of_lt_of_le entry (Nat.pow_le_pow_right (by norm_num) (by omega)))
  show ViewIdx input (.hot lane c ⟨n % chunkBits, _⟩ ⟨e % 2 ^ chunkBits, _⟩ half)
  refine ⟨?_, ?_, ?_, ?_⟩ <;> simp only [foldEq, entryEq] <;> assumption

theorem hashView_cell (cell : Cell) (label : Block) (inact : Inact input cell.1) :
    HashView input (cellInput cell label) := by
  unfold HashView
  rw [Kriterion.ArgoMAC.Phase3.Lazy.cellOf_cellInput]
  exact inact

theorem onQ_scale (lane : Lane) (c : Fin chunkCount) (j : Fin (2 ^ chunkWidth c))
    (limb : Fin (limbCount lane)) (label : Block)
    (inact : j ≠ chunkOf (Pipeline.coordBits (BitInput.ofAffine input) lane.coord) c) :
    OnQ input (.hash (scaleInput lane c j.val limb.val label)) := by
  have input' : scaleInput lane c j.val limb.val label = cellInput ⟨⟨lane, c, j⟩, limb⟩ label := rfl
  show HashView input (scaleInput lane c j.val limb.val label)
  rw [input']
  exact hashView_cell input ⟨⟨lane, c, j⟩, limb⟩ label inact

theorem onQ_bridge (t : BaseField) : OnQ input (.hash (bridgeInput t)) := by
  show HashView input (bridgeInput t)
  unfold HashView
  rw [cellOf_of_not_lt _ (bridgeInput_not_lt t)]
  exact bridgeInput_not_lt t

theorem onQ_gadget (o : Fin digitCount) (κ : Coord) (p : Fin PlanB.coordinateBits) (x : Block) :
    OnQ input (.fixedForward (.gadget o κ p) x) := trivial

theorem evalStepM_onQ (lane : Lane) (c : Fin chunkCount) (n : Nat) (small : n < chunkWidth c)
    (bitLabel join : Block) (parent : Fin (2 ^ n) → Block) :
    Hidden.QueryOnly (OnQ input) (Programs.evalStepM lane c n bitLabel join
      (activeAt (chunkValue (Pipeline.coordBits (BitInput.ofAffine input) lane.coord) c).toNat n)
      parent) := by
  unfold Programs.evalStepM
  refine Hidden.QueryOnly.bind (Hidden.QueryOnly.vector _ fun e => ?_) fun _ => Hidden.QueryOnly.pure' _
  by_cases active : e = activeAt (chunkValue (Pipeline.coordBits (BitInput.ofAffine input) lane.coord) c).toNat n
  · rw [if_pos active]
    exact Hidden.QueryOnly.pure' _
  · rw [if_neg active]
    have paid : 0 < n := by
      rcases Nat.eq_zero_or_pos n with zero | pos
      · subst zero
        exact absurd (Fin.ext (by have := e.isLt; simp at this; simp [activeAt])) active
      · exact pos
    have off : e.val ≠ activeEntry input lane c n := fun same => active (Fin.ext same)
    unfold Programs.foldMaskM
    exact Hidden.QueryOnly.bind (hashM_only _ _ (onQ_hot input lane c n e.val false _ paid small e.isLt off))
      fun _ => Hidden.QueryOnly.bind (hashM_only _ _ (onQ_hot input lane c n e.val true _ paid small e.isLt off))
        fun _ => Hidden.QueryOnly.pure' _

theorem evalFoldM_onQ (lane : Lane) (c : Fin chunkCount) (bitLabel join : Nat → Block) :
    ∀ steps, steps ≤ chunkWidth c → Hidden.QueryOnly (OnQ input) (Programs.evalFoldM lane c
      (chunkValue (Pipeline.coordBits (BitInput.ofAffine input) lane.coord) c).toNat bitLabel join steps)
  | 0, _ => Hidden.QueryOnly.pure' _
  | steps + 1, le =>
      Hidden.QueryOnly.bind (evalFoldM_onQ lane c bitLabel join steps (by omega)) fun _ =>
        Hidden.QueryOnly.bind (evalStepM_onQ input lane c steps (by omega) _ _ _) fun _ =>
          Hidden.QueryOnly.pure' _

theorem evalMasksM_onQ (lane : Lane) (c : Fin chunkCount) (hot : HotLabels (chunkWidth c)) :
    Hidden.QueryOnly (OnQ input) (Programs.evalMasksM lane c (chunkWidth c) hot
      (chunkOf (Pipeline.coordBits (BitInput.ofAffine input) lane.coord) c)) := by
  unfold Programs.evalMasksM
  refine Hidden.QueryOnly.bind (Hidden.QueryOnly.vector _ fun j => ?_) fun _ => Hidden.QueryOnly.pure' _
  by_cases active : j = chunkOf (Pipeline.coordBits (BitInput.ofAffine input) lane.coord) c
  · rw [if_pos active]
    exact Hidden.QueryOnly.pure' _
  · rw [if_neg active]
    unfold Programs.switchMaskM
    exact Hidden.QueryOnly.bind (Hidden.QueryOnly.vector _ fun limb =>
      Hidden.QueryOnly.ask _ (onQ_scale input lane c j limb (hot j) active)) fun _ =>
        Hidden.QueryOnly.pure' _

/-- **A lane of the evaluator asks only view questions.** -/
theorem evalLaneM_onQ (lane : Lane) (joins : Vector Block foldStepCount)
    (scale : Fin chunkCount → Fin (laneCount lane) → BaseField) (labels : Fin coordinateBitCount → Block) :
    Hidden.QueryOnly (OnQ input) (Programs.evalLaneM lane joins scale
      (Pipeline.coordBits (BitInput.ofAffine input) lane.coord) labels) := by
  refine Hidden.QueryOnly.bind (Hidden.QueryOnly.vector _ fun c => ?_) fun _ => Hidden.QueryOnly.pure' _
  unfold Programs.evalChunkM
  exact Hidden.QueryOnly.bind (evalFoldM_onQ input lane c _ _ _ le_rfl) fun _ =>
    Hidden.QueryOnly.bind (evalMasksM_onQ input lane c _) fun _ => Hidden.QueryOnly.pure' _

theorem padM_onQ (keys : WhiteningKeys) (coordinate : EncPRF.Coordinate)
    (index : Fin coordinateBitCount) (bit : Bool) :
    Hidden.QueryOnly (OnQ input) (Programs.padM keys coordinate index bit) :=
  Hidden.QueryOnly.bind (Hidden.QueryOnly.ask _ trivial) fun _ => Hidden.QueryOnly.pure' _

theorem curvePrefixM_onQ (P : Public) (mac : InputMac) :
    Hidden.QueryOnly (OnQ input) (curvePrefixM P (BitInput.ofAffine input) mac) := by
  unfold curvePrefixM
  exact Hidden.QueryOnly.bind (evalLaneM_onQ input .curveX _ _ _) fun _ =>
    Hidden.QueryOnly.bind (evalLaneM_onQ input .curveY _ _ _) fun _ =>
      Hidden.QueryOnly.ask _ (onQ_bridge input _)

/-- **The on-curve shadow asks only view questions.** -/
theorem shadow_onQ (P : Public) (mac : InputMac) :
    Hidden.QueryOnly (OnQ input) (shadowOnM P (BitInput.ofAffine input) mac) := by
  unfold shadowOnM
  refine Hidden.QueryOnly.bind (curvePrefixM_onQ input P mac) fun hashed =>
    Hidden.QueryOnly.bind ?_ fun _ => Hidden.QueryOnly.bind ?_ fun _ => Hidden.QueryOnly.pure' _
  · unfold truePadsM
    exact Hidden.QueryOnly.bind (Hidden.QueryOnly.vector _ fun _ => padM_onQ input _ _ _ _) fun _ =>
      Hidden.QueryOnly.bind (Hidden.QueryOnly.vector _ fun _ => padM_onQ input _ _ _ _) fun _ =>
        Hidden.QueryOnly.pure' _
  · unfold Programs.onCurveM
    refine Hidden.QueryOnly.bind (evalLaneM_onQ input .curveX _ _ _) fun _ =>
      Hidden.QueryOnly.bind (evalLaneM_onQ input .curveY _ _ _) fun _ =>
        Hidden.QueryOnly.bind (Hidden.QueryOnly.ask _ (onQ_bridge input _)) fun _ =>
          Hidden.QueryOnly.bind ?_ fun _ =>
            Hidden.QueryOnly.bind (evalLaneM_onQ input .pointX _ _ _) fun _ =>
              Hidden.QueryOnly.bind (evalLaneM_onQ input .pointY _ _ _) fun _ =>
                Hidden.QueryOnly.bind ?_ fun _ => Hidden.QueryOnly.pure' _
    · exact OnLaw.queryOnly_mono (Guess.evalPadsM_encOnly _ _) fun q ⟨_, _, _, same⟩ => by
        subst same
        trivial
    · exact OnLaw.queryOnly_mono (Guess.unlockM_asks _ _ _) fun q ⟨o, κ, p, same⟩ => by
        subst same
        exact onQ_gadget input o κ p _

/-! ### 3. The view of a table -/

open Classical in
/-- Fixed-key answers rebuilt from the view's. -/
def extFixed (x : VO input → Block) : FixedIndex → Block := fun i =>
  if h : ViewIdx input i then x ⟨i, h⟩ else 0

/-- A tape rebuilt from the inactive limbs. -/
def extTape (t : ICell input → Block × Block) : Tape := fun c =>
  if h : Inact input c.1 then t ⟨c, h⟩ else (0, 0)

/-- **The view's table.** -/
def viewTable (E : PermutationOracle EncPRF.PermutationIndex Block) (H : OtherTable)
    (x : VO input → Block) (t : ICell input → Block × Block) : Table :=
  (E, H, extFixed input x, extTape input t)

/-- **The shadow's transcript on a table is its transcript on the table's view.** -/
theorem transcript_view (A : Table) (P : Public) (mac : InputMac) :
    transcript (tableAnswer A) (shadowOnM P (BitInput.ofAffine input) mac) =
      transcript (tableAnswer (viewTable input A.1 A.2.1 (fun i => A.2.2.1 i.1)
        (fun c => A.2.2.2 c.1))) (shadowOnM P (BitInput.ofAffine input) mac) := by
  refine transcript_agree_only (shadow_onQ input P mac) _ _ fun q view => ?_
  cases q with
  | fixedForward index x =>
      have view' : ViewIdx input index := view
      show A.2.2.1 index = extFixed input (fun i => A.2.2.1 i.1) index
      unfold extFixed
      rw [dif_pos view']
  | fixedInverse _ _ => exact view.elim
  | encForward _ _ => rfl
  | encInverse _ _ => exact view.elim
  | hash key =>
      rw [tableAnswer_hash, tableAnswer_hash]
      cases found : cellOf key with
      | none => rfl
      | some cell =>
          have inact : Inact input cell.1 := by
            have holds : HashView input key := view
            unfold HashView at holds
            rw [found] at holds
            exact holds
          show A.2.2.2 cell = extTape input (fun c => A.2.2.2 c.1) cell
          unfold extTape
          rw [dif_pos inact]

/-! ### 4. The kernel -/

/-- **The kernel of `LawOn`'s both sides**: the weight at a published value, a key's selected
labels, and the shadow's transcript on a table planted on the empty oracle. -/
def onK (Ψ : Public → LamportSignature → LState → ℝ≥0∞) (P : Public) (key : InputMacKey)
    (A : Table) : ℝ≥0∞ :=
  Ψ P (Lamport.selectedLabels (key.encode (BitInput.ofAffine input)))
    (plantAll (transcript (tableAnswer A)
      (shadowOnM P (BitInput.ofAffine input) (key.encode (BitInput.ofAffine input)))) LazyOracle.empty)

/-- The kernel on the view. -/
def onKV (Ψ : Public → LamportSignature → LState → ℝ≥0∞) (P : Public) (key : InputMacKey)
    (E : PermutationOracle EncPRF.PermutationIndex Block) (H : OtherTable) (x : VO input → Block)
    (t : ICell input → Block × Block) : ℝ≥0∞ :=
  onK input Ψ P key (viewTable input E H x t)

/-- **The kernel reads a table only through its view.** -/
theorem onK_view (Ψ : Public → LamportSignature → LState → ℝ≥0∞) (P : Public) (key : InputMacKey)
    (A : Table) :
    onK input Ψ P key A = onKV input Ψ P key A.1 A.2.1 (fun i => A.2.2.1 i.1) (fun c => A.2.2.2 c.1) := by
  unfold onKV onK
  rw [transcript_view input A]

end

end Kriterion.ArgoMAC.Security.Phase3.PublicFirst.OnE
