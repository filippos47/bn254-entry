/-
**Stage 2, the valid arm, and `Stage2Law` modulo the opening law.**

* `opening_eq`: P3's `opening` is the intercepted run of `openingQueriesM`, then `openingLimbs`,
  then `programAll`;
* `opening_continuation`: through `OpeningLaw`, the oracle-free opening followed by any
  continuation that agrees on equal views is `openingLimbs` followed by it;
* `valid_law`: the valid arm (replay, opening, emission, parse) is P3's valid stage 2, from any
  memory satisfying `ReplayStart`, the output cells, the row constants and an empty response;
* `stage2Law_of_opening : OpeningLaw → Stage2Law` and
  `machineLaw_of_opening : OpeningLaw → MachineLaw planBSimulator machineCutoffError`.
-/

import Proof.Simulator.Stage2Start
import Proof.Simulator.MachineLaw

namespace Kriterion.ArgoMAC.PlanB.SimMachine

open BN254 Cryptography Cryptography.BoundedMachine Blocks GarbledCircuit
open Kriterion.ArgoMAC.Phase3.Glue

noncomputable section

/-! ### Abort-or-value binds -/

/-- Bind an abort-or-value law into an abort-or-value continuation. -/
def optBind {α γ : Type} (distribution : PMF (Option α)) (next : α → PMF (Option γ)) :
    PMF (Option γ) :=
  distribution.bind fun result => match result with
    | none => PMF.pure none
    | some value => next value

theorem optBind_map {α γ δ : Type} (distribution : PMF (Option α)) (next : α → PMF (Option γ))
    (f : γ → δ) :
    (optBind distribution next).map (Option.map f) =
      optBind distribution fun value => (next value).map (Option.map f) := by
  unfold optBind
  rw [PMF.map_bind]
  congr 1
  funext result
  cases result with
  | none => simp only [PMF.pure_map, Option.map_none]
  | some value => rfl

theorem optBind_bind {α γ δ : Type} (distribution : PMF (Option α)) (next : α → PMF (Option γ))
    (after : Option γ → PMF (Option δ)) (afterNone : after none = PMF.pure none) :
    (optBind distribution next).bind after =
      optBind distribution fun value => (next value).bind after := by
  unfold optBind
  rw [PMF.bind_bind]
  congr 1
  funext result
  cases result with
  | none => rw [PMF.pure_bind, afterNone]
  | some value => rfl

/-! ### The abstract opening, split -/

section Abstract

variable [FieldCertificate] [GroupCertificate] [DecidableEq PlanB.FixedIndex]
  [DecidableEq EncPRF.PermutationIndex]

/-- P3's opening: the intercepted replay, `openingLimbs`, then the programs. -/
theorem opening_eq (samplers : Samplers) (table : Public) (input : AffineInput)
    (labels : LamportSignature) (target : Point)
    (oracle : LazyOracle.State PlanB.FixedIndex EncPRF.PermutationIndex) :
    opening samplers table input labels target oracle =
      (runIntercept (BitInput.ofAffine input) (openingQueriesM table (BitInput.ofAffine input)
          (Lamport.restore input labels).inputMac) oracle noRecord).bind fun ran =>
        optBind (openingLimbs samplers table (BitInput.ofAffine input) target ran.1.1 ran.1.2)
          fun answers =>
            PMF.pure (programAll (programRequests (BitInput.ofAffine input) ran.2.2 answers)
              ran.2.1) := by
  unfold opening optBind
  dsimp only
  congr 1
  funext ran
  congr 1
  funext answers
  cases answers <;> rfl

/-- Decode the limbs of a view: limb `i` from half cells `2i`, `2i + 1`. -/
def decodeView (view : OpenView) : DesignatedLimbs :=
  fun limb => (BitVec.ofNat 128 (view.1 ⟨2 * limb.val, by omega⟩).toNat,
    BitVec.ofNat 128 (view.1 ⟨2 * limb.val + 1, by omega⟩).toNat)

omit [FieldCertificate] [GroupCertificate] [DecidableEq PlanB.FixedIndex]
  [DecidableEq EncPRF.PermutationIndex] in
theorem decodeView_blocks (memory : Memory) (answers : DesignatedLimbs) :
    decodeView (blocksView memory answers) = answers := by
  funext limb
  simp only [decodeView, blocksView, blockWord_block]
  rw [limbHalf_low answers limb.val limb.isLt, limbHalf_high answers limb.val limb.isLt]

omit [DecidableEq PlanB.FixedIndex] [DecidableEq EncPRF.PermutationIndex] in
/-- **The opening law, applied**: the oracle-free opening followed by a continuation `C` is
`openingLimbs` followed by `H`, when `C` and `H` agree on equal views. -/
theorem opening_continuation (law : OpeningLaw) (source : Stage1Source) (input : AffineInput)
    (target : Point) (pointX : Fin pointElementCountX → BaseField)
    (pointY : Fin pointElementCountY → BaseField) (memory : Memory)
    (pre : OpeningPre source input target pointX pointY memory) {γ : Type}
    (C : Memory → PMF (Option γ)) (H : DesignatedLimbs → PMF (Option γ))
    (agree : ∀ next answers, openView next = blocksView memory answers → C next = H answers) :
    optBind (openingFree.memSem memory) C =
      optBind (openingLimbs boundedSamplers source.publicValue (BitInput.ofAffine input) target
          pointX pointY) H := by
  have equal := law source input target pointX pointY memory pre
  have step : optBind (openingFree.memSem memory) C =
      (openingFree.memSem memory).bind (fun result => match Option.map openView result with
        | none => PMF.pure none
        | some view => H (decodeView view)) := by
    unfold optBind
    apply PMF.bind_congr
    intro result member
    cases result with
    | none => rfl
    | some next =>
        have mapped : some (openView next) ∈
            ((openingFree.memSem memory).map (Option.map openView)).support :=
          (PMF.mem_support_map_iff _ _ _).2 ⟨some next, member, rfl⟩
        rw [equal] at mapped
        obtain ⟨drawn, _, same⟩ := (PMF.mem_support_map_iff _ _ _).1 mapped
        cases drawn with
        | none => cases same
        | some blocks =>
            injection same with same
            show C next = H (decodeView (openView next))
            rw [← same, decodeView_blocks]
            exact agree next blocks same.symm
  rw [step]
  have mapBind : ∀ (distribution : PMF (Option Memory)),
      distribution.bind (fun result => match Option.map openView result with
        | none => PMF.pure none
        | some view => H (decodeView view)) =
      (distribution.map (Option.map openView)).bind fun result => match result with
        | none => PMF.pure none
        | some view => H (decodeView view) := by
    intro distribution
    rw [PMF.bind_map]
    rfl
  rw [mapBind, equal, PMF.bind_map]
  unfold optBind
  congr 1
  funext drawn
  cases drawn with
  | none => rfl
  | some blocks =>
      show H (decodeView (blocksView memory blocks)) = H blocks
      rw [decodeView_blocks]

end Abstract

/-! ### The valid arm -/

section Valid

variable [FieldCertificate] [DecidableEq PlanB.FixedIndex] [DecidableEq EncPRF.PermutationIndex]

/-- The protocol's parse of the valid arm's result. -/
def finishK (final : Option (Memory × OState PlanB.FixedIndex EncPRF.PermutationIndex)) :
    PMF (Option (LamportSignature × OState PlanB.FixedIndex EncPRF.PermutationIndex)) :=
  match final with
  | none => PMF.pure none
  | some (last, updated) => PMF.pure ((SimulatorProtocol.words 128 508 (last.bits 3)).map
      fun labels => (labels, updated))

omit [FieldCertificate] [DecidableEq PlanB.FixedIndex] [DecidableEq EncPRF.PermutationIndex] in
theorem labelVector_of (ram : Word → Word) (labels : LamportSignature)
    (cells : ∀ (i : Nat) (bound : i < 508), ram (word (labelBase + i)) = blockWord (labels[i]'bound)) :
    labelVector ram = labels := by
  apply Vector.ext
  intro i bound
  simp only [labelVector, Vector.getElem_ofFn]
  rw [cells i bound, blockWord_block]

/-- The emission and the parse, after the programs. -/
theorem emit_finish (after : Memory) (labels : LamportSignature)
    (vector : labelVector after.ram = labels) (empty : after.bits 3 = [])
    (updated : OState PlanB.FixedIndex EncPRF.PermutationIndex) :
    (rsem (.seq Request.emitLabels (.skip 0)) after updated).bind finishK =
      PMF.pure (some (labels, updated)) := by
  obtain ⟨last, runEmit, _, bitsEmit, _⟩ := memSem_emitLabels after
  rw [rsem_seq_skip,
    show rsem Request.emitLabels after updated =
      (Request.emitLabels.memSem after).map (Option.map fun next => (next, updated)) from
      @sem_noOracle _ PlanB.FixedIndex EncPRF.PermutationIndex (Fintype.ofFinite _)
        (Fintype.ofFinite _) _ _ Request.emitLabels invalid_noOracle after updated,
    runEmit, PMF.pure_map, Option.map_some, PMF.pure_bind]
  show PMF.pure ((SimulatorProtocol.words 128 508 (last.bits 3)).map fun labels => (labels, updated)) = _
  rw [bitsEmit, empty, List.append_nil, labelRuns_words, vector]
  rfl


/-- The opening followed by any rest, split at the oracle-free part. -/
theorem rsem_seq_opening (rest : Prog) (memory : Memory)
    (oracle : OState PlanB.FixedIndex EncPRF.PermutationIndex) :
    rsem (.seq Opening.program rest) memory oracle =
      optBind (openingFree.memSem memory) fun next =>
        andThen (rsem (Prog.seqList [Opening.programs, zeroRegs allRegisters])) (rsem rest) next
          oracle := by
  rw [rsem_seq]
  unfold andThen
  rw [rsem_opening]
  unfold optBind
  rw [PMF.bind_bind]
  congr 1
  funext result
  cases result with
  | none => rw [PMF.pure_bind]
  | some next => rfl

omit [FieldCertificate] [DecidableEq PlanB.FixedIndex] [DecidableEq EncPRF.PermutationIndex] in
theorem optBind_finishK {α : Type} (distribution : PMF (Option α))
    (next : α → PMF (Option (Memory × OState PlanB.FixedIndex EncPRF.PermutationIndex))) :
    (optBind distribution next).bind finishK = optBind distribution fun value => (next value).bind finishK :=
  optBind_bind _ _ _ rfl

/-- The machine's continuation after the replay. -/
def machineRest (memory : Memory) (updated : OState PlanB.FixedIndex EncPRF.PermutationIndex) :
    PMF (Option (LamportSignature × OState PlanB.FixedIndex EncPRF.PermutationIndex)) :=
  (rsem (.seq Opening.program (.seq Request.emitLabels (.skip 0))) memory updated).bind finishK

/-- The abstract continuation after the replay. -/
def abstractRest [GroupCertificate] (source : Stage1Source) (input : AffineInput)
    (labels : LamportSignature) (target : Point)
    (value : ((Fin pointElementCountX → BaseField) × (Fin pointElementCountY → BaseField)) ×
      DesignatedRecord)
    (updated : OState PlanB.FixedIndex EncPRF.PermutationIndex) :
    PMF (Option (LamportSignature × OState PlanB.FixedIndex EncPRF.PermutationIndex)) :=
  (optBind (openingLimbs boundedSamplers source.publicValue (BitInput.ofAffine input) target
      value.1.1 value.1.2) fun answers =>
    PMF.pure (programAll (programRequests (BitInput.ofAffine input) value.2 answers) updated)).map
    (Option.map fun updated => (labels, updated))

/-- Run a machine tree and continue on its non-aborting leaves. -/
def leafBind {δ : Type}
    (distribution : PMF (Option Memory × OState PlanB.FixedIndex EncPRF.PermutationIndex))
    (onMachine : Memory → OState PlanB.FixedIndex EncPRF.PermutationIndex → PMF (Option δ)) :
    PMF (Option δ) :=
  distribution.bind fun result => match result.1 with
    | none => PMF.pure none
    | some memory => onMachine memory result.2

omit [FieldCertificate] [DecidableEq PlanB.FixedIndex] [DecidableEq EncPRF.PermutationIndex] in
theorem openView_labels (memory : Memory) : (openView memory).2.2.2.1 = labelVector memory.ram := by
  unfold openView
  rfl

omit [FieldCertificate] [DecidableEq PlanB.FixedIndex] [DecidableEq EncPRF.PermutationIndex] in
theorem blocksView_labels (memory : Memory) (answers : DesignatedLimbs) :
    (blocksView memory answers).2.2.2.1 = labelVector memory.ram := by
  unfold blocksView
  rfl

/-- **The continuations agree** on the replay's post-condition. -/
theorem valid_agree [GroupCertificate] (law : OpeningLaw) (source : Stage1Source)
    (input : AffineInput) (labels : LamportSignature) (target : Point) (middle : Memory)
    (start : ReplayStart source input labels middle)
    (outputs : (middle.ram (word reqTag0), middle.ram (word reqQX), middle.ram (word reqQY)) =
      outputWords target)
    (rows : ∀ (digit : Fin digitCount) (slot : Nat), slot < 10 →
      middle.ram (word (Opening.rowCell digit.val slot)) =
        fieldWord (rowField (source.rows.get digit) slot))
    (empty : middle.bits 3 = [])
    (value : ((Fin pointElementCountX → BaseField) × (Fin pointElementCountY → BaseField)) ×
      DesignatedRecord)
    (memory : Memory) (o : OState PlanB.FixedIndex EncPRF.PermutationIndex)
    (post : ReplayPost (BitInput.ofAffine input) middle value memory) :
    machineRest memory o = abstractRest source input labels target value o := by
  obtain ⟨accX, accY, jstarCell, kappaCell, ⟨star, starCell, recorded⟩, frame, bitsSame⟩ := post
  have labelsAt : labelVector memory.ram = labels := labelVector_of _ _ fun i bound => by
    rw [frame _ (offReplay_of_lt (label_small i bound))]
    exact start.labelCells i bound
  have pre : OpeningPre source input target value.1.1 value.1.2 memory :=
    { reqXCell := by rw [frame _ (offReplay_of_lt reqX_small)]; exact start.reqXCell
      reqYCell := by rw [frame _ (offReplay_of_lt reqY_small)]; exact start.reqYCell
      outputCells := by
        rw [frame (word reqTag0) (offReplay_of_lt (by unfold reqTag0 requestBase; norm_num)),
          frame (word reqQX) (offReplay_of_lt (by unfold reqQX requestBase; norm_num)),
          frame (word reqQY) (offReplay_of_lt (by unfold reqQY requestBase; norm_num))]
        exact outputs
      rowCells := fun digit slot small => by
        have := digit.isLt
        unfold digitCount at this
        rw [frame (word (Opening.rowCell digit.val slot)) (offReplay_of_lt (by
          unfold Opening.rowCell fieldBase curveCellCount; omega))]
        exact rows digit slot small
      accXCells := accX
      accYCells := accY
      kappaCell := kappaCell }
  unfold machineRest abstractRest
  rw [rsem_seq_opening, optBind_finishK, optBind_map]
  refine opening_continuation law source input target value.1.1 value.1.2 memory pre _ _ ?_
  intro next answers same
  have halves : ∀ half : Fin (2 * limbCount .pointX),
      next.ram (word (halfCell half.val)) = blockWord (limbHalf answers half) := fun half =>
    congrFun (congrArg Prod.fst same) half
  have jstar' : next.ram (word tmpJStar) = memory.ram (word tmpJStar) :=
    congrArg (fun view : OpenView => view.2.1) same
  have star' : next.ram (word designatedLabel) = memory.ram (word designatedLabel) :=
    congrArg (fun view : OpenView => view.2.2.1) same
  have labels' : labelVector next.ram = labelVector memory.ram := by
    rw [← openView_labels, ← blocksView_labels memory answers, same]
  have bits' : next.bits 3 = memory.bits 3 := congrArg (fun view : OpenView => view.2.2.2.2) same
  obtain ⟨after, afterRam, afterBits, runTail⟩ := rsem_programsTail (BitInput.ofAffine input)
    answers star next (star'.trans starCell) halves (jstar'.trans jstarCell)
  show (andThen _ _ next o).bind finishK = _
  unfold andThen
  rw [runTail o, PMF.pure_bind, PMF.pure_map, recorded]
  cases programAll (programRequests (BitInput.ofAffine input) (fun _ => some star) answers) o with
  | none =>
      show (PMF.pure none).bind finishK = PMF.pure none
      rw [PMF.pure_bind]
      rfl
  | some updated =>
      show (rsem (.seq Request.emitLabels (.skip 0)) after updated).bind finishK =
        PMF.pure (some (labels, updated))
      exact emit_finish after labels (by rw [afterRam, labels', labelsAt])
        (by rw [afterBits, bits', bitsSame, empty]) updated

/-- The machine's valid arm, as the replay tree followed by `machineRest`. -/
theorem valid_machine (middle : Memory) (oracle : OState PlanB.FixedIndex EncPRF.PermutationIndex) :
    (rsem (Stage2.valid ordF0 ordE0) middle oracle).bind finishK =
      leafBind (runT (rtree (Replay.program ordF0 ordE0) middle) oracle) machineRest := by
  unfold Stage2.valid leafBind
  simp only [Prog.seqList]
  rw [rsem_seq]
  unfold andThen
  rw [show rsem (Replay.program ordF0 ordE0) middle oracle =
      (runT (rtree (Replay.program ordF0 ordE0) middle) oracle).map lower from
    @sem_eq_runT _ PlanB.FixedIndex EncPRF.PermutationIndex (Fintype.ofFinite _)
      (Fintype.ofFinite _) _ _ _ (replay_treeOps ordF0 ordE0) middle oracle,
    PMF.bind_map, PMF.bind_bind]
  congr 1
  funext result
  rcases result with ⟨_ | memory, updated⟩
  · show (PMF.pure none).bind finishK = PMF.pure none
    rw [PMF.pure_bind]
    rfl
  · rfl

/-- P3's valid stage 2, as the intercepted tree followed by `abstractRest`. -/
theorem valid_abstract [GroupCertificate] (source : Stage1Source) (input : AffineInput)
    (labels : LamportSignature) (target : Point)
    (oracle : OState PlanB.FixedIndex EncPRF.PermutationIndex) :
    (opening boundedSamplers source.publicValue input labels target oracle).map
        (Option.map fun updated => (labels, updated)) =
      (runT (interceptT (BitInput.ofAffine input) (openingQueriesM source.publicValue
          (BitInput.ofAffine input) (Lamport.restore input labels).inputMac) fun _ => none)
          oracle).bind fun result => abstractRest source input labels target result.1 result.2 := by
  rw [opening_eq, runIntercept_eq_runT, PMF.bind_map, PMF.map_bind]
  rfl

omit [FieldCertificate] in
/-- **Agreeing trees, run with the leaf binder.** -/
theorem agree_leafBind {β δ : Type} {Post : β → Memory → Prop}
    (onMachine : Memory → OState PlanB.FixedIndex EncPRF.PermutationIndex → PMF (Option δ))
    (onAbstract : β → OState PlanB.FixedIndex EncPRF.PermutationIndex → PMF (Option δ))
    (agreeing : ∀ value memory oracle, Post value memory → onMachine memory oracle = onAbstract value oracle)
    {tree : FreeQuery Programs.Spec (Option Memory)} {tree' : FreeQuery Programs.Spec β}
    (agree : Agree Post tree tree') (oracle : OState PlanB.FixedIndex EncPRF.PermutationIndex) :
    leafBind (runT tree oracle) onMachine = (runT tree' oracle).bind fun result =>
      onAbstract result.1 result.2 := by
  rw [← agree_run onMachine onAbstract agreeing agree oracle]
  unfold leafBind
  congr 1

/-- **The valid arm**: replay, opening, emission and parse are P3's valid stage 2. -/
theorem valid_law [GroupCertificate] (law : OpeningLaw) (source : Stage1Source)
    (input : AffineInput) (labels : LamportSignature) (target : Point) (middle : Memory)
    (start : ReplayStart source input labels middle)
    (outputs : (middle.ram (word reqTag0), middle.ram (word reqQX), middle.ram (word reqQY)) =
      outputWords target)
    (rows : ∀ (digit : Fin digitCount) (slot : Nat), slot < 10 →
      middle.ram (word (Opening.rowCell digit.val slot)) =
        fieldWord (rowField (source.rows.get digit) slot))
    (empty : middle.bits 3 = []) (oracle : OState PlanB.FixedIndex EncPRF.PermutationIndex) :
    (rsem (Stage2.valid ordF0 ordE0) middle oracle).bind finishK =
      (opening boundedSamplers source.publicValue input labels target oracle).map
        (Option.map fun updated => (labels, updated)) := by
  rw [valid_machine, valid_abstract]
  exact agree_leafBind machineRest (abstractRest source input labels target)
    (fun value memory o post => valid_agree law source input labels target middle start outputs rows
      empty value memory o post)
    (agree_replay source input labels middle start) oracle

end Valid

/-! ### The kernels -/

/-- **The machine's stage 2 on a defined output**: the valid arm from the prefix's memory, then
the protocol's parse. -/
theorem machine_stage2_some [FieldCertificate] (initial : Configuration (planBSimulator.size + 1))
    (input : AffineInput) (target : Point)
    (oracle : LazyOracle.State PlanB.FixedIndex EncPRF.PermutationIndex) (middle : Memory)
    (runPrefix : Request.prefixProgram.memSem (prefixStart initial.memory input target) =
      PMF.pure (some middle))
    (flag : middle.registers rFlag ≠ 0) :
    (machineKernels).stage2 initial input (some target) oracle =
      (@rsem _ (Classical.decEq _) (Classical.decEq _) (Stage2.valid ordF0 ordE0) middle
        oracle).bind finishK := by
  unfold machineKernels machineAbstract
  dsimp only
  have run := planB_stage2_run initial.memory input (some target) oracle
  rw [show Top.afterTag (stage2Memory initial.memory input (some target))
      (stage2Rest input (some target)) = prefixStart initial.memory input target from rfl,
    runPrefix, PMF.pure_bind] at run
  simp only [flag, if_false] at run
  rw [show (⟨Function.update (Function.update initial.memory.bits 0
      ([false, true] ++ SimulatorProtocol.affine input ++ SimulatorProtocol.output (some target))) 3 [],
      initial.memory.registers, initial.memory.ram⟩ : Memory) =
      stage2Memory initial.memory input (some target) from rfl, run]
  rw [OptionT.run_bind, OptionT.run_mk]
  simp only [Option.elimM, PMF.monad_bind_eq_bind, PMF.bind_bind]
  congr 1
  funext final
  rcases final with _ | ⟨last, updated⟩
  · simp only [PMF.pure_bind, Option.elim, finishK]
    rfl
  · simp only [PMF.pure_bind, Option.elim, finishK, atPc_memory, OptionT.run_bind, OptionT.run_mk,
      Option.elimM, PMF.monad_bind_eq_bind]
    cases SimulatorProtocol.words 128 508 (last.bits 3) <;> rfl

/-- **`Stage2Law`, modulo the opening law** (`OpeningLaw`, `Stage2Spec.lean`): the invalid arm is
`stage2Law_none`; the valid arm is the prefix, the replay, the opening, the `362` programs and the
emission. -/
theorem stage2Law_of_opening (law : OpeningLaw) : Stage2Law := by
  intro field group parameter result member input output oracle
  cases output with
  | none => exact stage2Law_none result.2.1 input oracle
  | some target =>
      obtain ⟨draw, drawMember, retainedIs⟩ := stage1_support parameter result member
      obtain ⟨middle, run, flag, empty, parsed, labels⟩ :=
        prefix_middle (retained parameter draw) input target
      have start := prefix_replayStart parameter draw drawMember input target middle parsed labels
      have outputs := prefix_output _ middle input target parsed
      have rows := prefix_rows parameter draw input target middle parsed
      rw [machine_stage2_some result.2.1 input target oracle middle (by rw [retainedIs]; exact run)
        flag, retainedIs]
      unfold retained
      rw [extractSource_final]
      exact (@valid_law _ (Classical.decEq _) (Classical.decEq _) _ law (drawSource draw) input _
        target middle start outputs rows empty oracle).symm

/-- **P3's machine law for the Plan B machine, modulo the opening law.** -/
theorem machineLaw_of_opening (law : OpeningLaw) : MachineLaw planBSimulator machineCutoffError :=
  machineLaw_of_stage2 (stage2Law_of_opening law)

end

end Kriterion.ArgoMAC.PlanB.SimMachine
