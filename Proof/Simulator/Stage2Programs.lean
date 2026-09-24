/-
**Stage 2, the program batch** (`rsem_programs`): the `452` machine programs of
`Opening.programs` (limb `i`: `hash (E* + 2^128 · scaleTag pointX 0 j* i) := (V_i mod 2^128,
V_i / 2^128)`, the halves read from the preimage sampler's half cells) are P3's
`programAll (programRequests bits (fun _ => some E*) …)`, from any memory holding `E*`, `j*` and
the halves; the RAM and the stacks are unchanged. Also: the split of `Opening.program` into
`openingFree` and the batch, and the oracle-freeness of `openingFree`.
-/

import Proof.Simulator.ReplayProgram
import Proof.Simulator.OpeningPreimage

namespace Kriterion.ArgoMAC.PlanB.SimMachine

open BN254 Cryptography Cryptography.BoundedMachine Blocks GarbledCircuit
open Kriterion.ArgoMAC.Phase3.Glue

noncomputable section

variable [FieldCertificate] [DecidableEq PlanB.FixedIndex] [DecidableEq EncPRF.PermutationIndex]

/-- A machine block's law at the `planBSimulator` index instances. -/
abbrev rsem (program : Prog) (memory : Memory)
    (oracle : OState PlanB.FixedIndex EncPRF.PermutationIndex) :
    PMF (Option (Memory × OState PlanB.FixedIndex EncPRF.PermutationIndex)) :=
  @Prog.sem _ PlanB.FixedIndex EncPRF.PermutationIndex (Fintype.ofFinite _) (Fintype.ofFinite _) _ _
    program memory oracle

/-! ### Sequencing -/

theorem rsem_seq (first second : Prog) (memory : Memory)
    (oracle : OState PlanB.FixedIndex EncPRF.PermutationIndex) :
    rsem (.seq first second) memory oracle = andThen (rsem first) (rsem second) memory oracle := rfl

theorem rsem_seq_pure (first rest : Prog) (memory after : Memory)
    (oracle : OState PlanB.FixedIndex EncPRF.PermutationIndex)
    (run : rsem first memory oracle = PMF.pure (some (after, oracle))) :
    rsem (.seq first rest) memory oracle = rsem rest after oracle := by
  rw [rsem_seq]
  unfold andThen
  rw [run, PMF.pure_bind]

theorem rsem_seq_skip (first : Prog) (count : Nat) (memory : Memory)
    (oracle : OState PlanB.FixedIndex EncPRF.PermutationIndex) :
    rsem (.seq first (.skip count)) memory oracle = rsem first memory oracle := by
  rw [rsem_seq]
  unfold andThen
  conv_rhs => rw [← PMF.bind_pure (rsem first memory oracle)]
  congr 1
  funext result
  rcases result with _ | ⟨next, updated⟩ <;> rfl

theorem rsem_skip (count : Nat) (memory : Memory)
    (oracle : OState PlanB.FixedIndex EncPRF.PermutationIndex) :
    rsem (.skip count) memory oracle = PMF.pure (some (memory, oracle)) := rfl

/-- `seqList` of an append is the sequence of the two parts. -/
theorem rsem_seqList_append (first second : List Prog) (memory : Memory)
    (oracle : OState PlanB.FixedIndex EncPRF.PermutationIndex) :
    rsem (Prog.seqList (first ++ second)) memory oracle =
      andThen (rsem (Prog.seqList first)) (rsem (Prog.seqList second)) memory oracle := by
  induction first generalizing memory oracle with
  | nil =>
      rw [List.nil_append]
      show _ = andThen (rsem (.skip 0)) _ memory oracle
      unfold andThen
      rw [rsem_skip, PMF.pure_bind]
  | cons head rest ih =>
      rw [List.cons_append]
      show rsem (.seq head (Prog.seqList (rest ++ second))) memory oracle =
        andThen (rsem (.seq head (Prog.seqList rest))) _ memory oracle
      rw [rsem_seq]
      unfold andThen
      rw [rsem_seq]
      unfold andThen
      rw [PMF.bind_bind]
      congr 1
      funext result
      rcases result with _ | ⟨next, updated⟩
      · simp only [PMF.pure_bind]
      · exact ih next updated

/-- A tree block runs as its tree. -/
theorem rsem_of_tree (program : Prog) (ops : program.OpsSatisfy TreeOp) (memory after : Memory)
    (run : rtree program memory = .pure (some after))
    (oracle : OState PlanB.FixedIndex EncPRF.PermutationIndex) :
    rsem program memory oracle = PMF.pure (some (after, oracle)) := by
  rw [rsem, @sem_eq_runT _ PlanB.FixedIndex EncPRF.PermutationIndex (Fintype.ofFinite _)
    (Fintype.ofFinite _) _ _ program ops memory oracle]
  change (runT (rtree program memory) oracle).map lower = _
  rw [run]
  simp [runT, lower, PMF.pure_map]

/-! ### One program -/

theorem rsem_loadAt_seq (target : Register) (address : Nat) (rest : Prog) (memory : Memory)
    (oracle : OState PlanB.FixedIndex EncPRF.PermutationIndex) :
    rsem (.seq (loadAt target address) rest) memory oracle =
      rsem rest (setReg (setReg memory rAddr (word address)) target (memory.ram (word address)))
        oracle :=
  rsem_seq_pure _ _ _ _ _ (rsem_of_tree (loadAt target address) ⟨trivial, trivial⟩ memory _ rfl oracle)

theorem rsem_cst_seq (target : Register) (value : Nat) (rest : Prog) (memory : Memory)
    (oracle : OState PlanB.FixedIndex EncPRF.PermutationIndex) :
    rsem (.seq (cst target value) rest) memory oracle =
      rsem rest (setReg memory target (word value)) oracle :=
  rsem_seq_pure _ _ _ _ _ (rsem_of_tree (cst target value) trivial memory _ rfl oracle)

theorem rsem_ar_seq (operation : Arithmetic) (target left right : Register) (rest : Prog)
    (memory : Memory) (oracle : OState PlanB.FixedIndex EncPRF.PermutationIndex) :
    rsem (.seq (ar operation target left right) rest) memory oracle =
      rsem rest (setReg memory target
        (operation.eval (memory.registers left) (memory.registers right))) oracle :=
  rsem_seq_pure _ _ _ _ _ (rsem_of_tree (ar operation target left right) trivial memory _ rfl oracle)

omit [DecidableEq PlanB.FixedIndex] [DecidableEq EncPRF.PermutationIndex] in
/-- The designated input of limb `i` in the machine's arithmetic: `E* + 2^128 · 512 · j*` plus
`2^128 · scaleTag pointX 0 0 i`. -/
theorem designatedInput_nat (bits : BitInput) (limb : Fin (limbCount .pointX)) (star : Block) :
    designatedInput bits limb star =
      (((designatedSwitch bits).val * (2 ^ 128 * 512) + 2 ^ 128 * scaleTag .pointX 0 0 limb.val +
        star.toNat : Nat) : BaseField) := by
  have jSmall : (designatedSwitch bits).val < 4 :=
    lt_of_lt_of_eq (designatedSwitch bits).isLt twoPow_chunkWidth_chunkZero
  have limbSmall : limb.val < 452 := limb.isLt
  unfold designatedInput scaleInput
  congr 1
  unfold scaleTag scaleTagWith chunkBits
  rw [Nat.mod_eq_of_lt (by omega : (designatedSwitch bits).val < 2 ^ 5),
    Nat.mod_eq_of_lt (by omega : limb.val < 512), show laneCode .pointX = 2 from rfl]
  show star.toNat + 2 ^ 128 * (((2 * chunkCount + 0) * 2 ^ 5 + (designatedSwitch bits).val) * 512 +
    limb.val) = _
  unfold chunkCount
  ring

/-- A hash program on decoded registers. -/
theorem rsem_programHash (memory : Memory) (oracle : OState PlanB.FixedIndex EncPRF.PermutationIndex)
    (input : BaseField) (low high : Block)
    (hInput : ((memory.registers rInput).toNat : BaseField) = input)
    (hFirst : memory.registers rFirst = blockWord low)
    (hSecond : memory.registers rSecond = blockWord high) :
    rsem (.op (.program 4 rIndex rInput rFirst rSecond)) memory oracle =
      PMF.pure ((LazyOracle.program (.hash input) (low, high) oracle).map
        fun updated => (memory, updated)) := by
  subst hInput
  simp only [rsem, Prog.sem, Op.sem]
  rw [query_hash]
  simp only [answerFromWords]
  rw [hFirst, hSecond, blockWord_block, blockWord_block]

/-- **One program**: `hash (designatedInput bits i E*) := (low half, high half)`. -/
theorem rsem_programOne (bits : BitInput) (limb : Fin (limbCount .pointX)) (memory : Memory)
    (star low high : Block)
    (starCell : memory.ram (word designatedLabel) = blockWord star)
    (lowCell : memory.ram (word (halfCell (2 * limb.val))) = blockWord low)
    (highCell : memory.ram (word (halfCell (2 * limb.val + 1))) = blockWord high)
    (jCell : memory.ram (word tmpJStar) = word (designatedSwitch bits).val) :
    ∃ after, after.ram = memory.ram ∧ after.bits = memory.bits ∧ ∀ oracle,
      rsem (Opening.programOne limb.val) memory oracle =
        PMF.pure ((LazyOracle.program (.hash (designatedInput bits limb star)) (low, high)
          oracle).map fun updated => (after, updated)) := by
  have jSmall : (designatedSwitch bits).val < 4 :=
    lt_of_lt_of_eq (designatedSwitch bits).isLt twoPow_chunkWidth_chunkZero
  have limbSmall : limb.val < 452 := limb.isLt
  have tagSmall : scaleTag .pointX 0 0 limb.val < 2 ^ 21 := by
    unfold scaleTag scaleTagWith chunkCount chunkBits
    rw [show laneCode .pointX = 2 from rfl]
    omega
  have starSmall : star.toNat < 2 ^ 128 := star.isLt
  have lowCell' : memory.ram (word (BigInt.halfBase samplerBase BigInt.samplerLimbs +
      2 * limb.val)) = blockWord low := lowCell
  have highCell' : memory.ram (word (BigInt.halfBase samplerBase BigInt.samplerLimbs +
      2 * limb.val + 1)) = blockWord high := highCell
  have starWord : blockWord star = word star.toNat := rfl
  refine ⟨?after, ?ram, ?bits, fun oracle => ?run⟩
  case run =>
    unfold Opening.programOne
    simp only [Prog.seqList]
    rw [rsem_loadAt_seq, rsem_loadAt_seq, rsem_loadAt_seq, rsem_cst_seq, rsem_ar_seq,
      rsem_cst_seq, rsem_ar_seq, rsem_loadAt_seq, rsem_ar_seq, rsem_seq_skip]
    rw [rsem_programHash _ oracle (designatedInput bits limb star) low high ?hIn ?hLow ?hHigh]
    case hIn =>
      simp (config := {decide := true}) only [setReg_registers, setReg_ram, reduceIte]
      rw [jCell, starCell, starWord, BigInt.eval_mul_word, BigInt.eval_add_word,
        BigInt.eval_add_word, BigInt.toNat_word_of_lt (by omega), designatedInput_nat]
    case hLow =>
      simp (config := {decide := true}) only [setReg_registers, setReg_ram, reduceIte]
      exact lowCell'
    case hHigh =>
      simp (config := {decide := true}) only [setReg_registers, setReg_ram, reduceIte]
      exact highCell'
  case ram => simp only [setReg_ram]
  case bits => simp only [setReg_bits]

/-! ### The batch -/

omit [FieldCertificate] in
theorem programAll_append (first second : List (Option BaseField × (Block × Block)))
    (oracle : OState PlanB.FixedIndex EncPRF.PermutationIndex) :
    programAll (first ++ second) oracle = (programAll first oracle).bind (programAll second) := by
  induction first generalizing oracle with
  | nil => rfl
  | cons head rest ih =>
      obtain ⟨input, answer⟩ := head
      cases input with
      | none => rfl
      | some input =>
          simp only [List.cons_append, programAll]
          rw [Option.bind_assoc]
          congr 1
          funext updated
          exact ih updated

omit [FieldCertificate] in
theorem programAll_single (input : BaseField) (answer : Block × Block)
    (oracle : OState PlanB.FixedIndex EncPRF.PermutationIndex) :
    programAll [(some input, answer)] oracle = LazyOracle.program (.hash input) answer oracle := by
  show (LazyOracle.program (.hash input) answer oracle).bind (programAll []) = _
  cases LazyOracle.program (.hash input) answer oracle <;> rfl

omit [FieldCertificate] [DecidableEq PlanB.FixedIndex] [DecidableEq EncPRF.PermutationIndex] in
theorem finRange_flatMap_succ {β : Type} (count : Nat) (f : Nat → List β) :
    (List.finRange (count + 1)).flatMap (fun index => f index.val) =
      (List.finRange count).flatMap (fun index => f index.val) ++ f count := by
  rw [List.finRange_succ_last, List.flatMap_append, List.flatMap_map]
  simp

/-- **A batch of programs**: a `rep` whose steps are programs is the program list. -/
theorem rsem_rep_programs (count : Nat) (body : Nat → Prog)
    (requests : Nat → List (Option BaseField × (Block × Block))) (ram0 : Word → Word)
    (bits0 : Fin 4 → List Bool)
    (step : ∀ index memory, index < count → memory.ram = ram0 → memory.bits = bits0 →
      ∃ after, after.ram = ram0 ∧ after.bits = bits0 ∧ ∀ oracle,
        rsem (body index) memory oracle =
          PMF.pure ((programAll (requests index) oracle).map fun updated => (after, updated))) :
    ∀ done memory, done ≤ count → memory.ram = ram0 → memory.bits = bits0 →
      ∃ after, after.ram = ram0 ∧ after.bits = bits0 ∧ ∀ oracle,
        rsem (Prog.rep done body) memory oracle =
          PMF.pure ((programAll ((List.finRange done).flatMap fun index => requests index.val)
            oracle).map fun updated => (after, updated))
  | 0, memory, _, ram, bits => ⟨memory, ram, bits, fun oracle => by rw [Prog.rep]; rfl⟩
  | done + 1, memory, bound, ram, bits => by
      obtain ⟨middle, middleRam, middleBits, run⟩ :=
        rsem_rep_programs count body requests ram0 bits0 step done memory (by omega) ram bits
      obtain ⟨after, afterRam, afterBits, run'⟩ := step done middle (by omega) middleRam middleBits
      refine ⟨after, afterRam, afterBits, fun oracle => ?_⟩
      rw [Prog.rep, rsem_seq]
      unfold andThen
      rw [run, PMF.pure_bind, finRange_flatMap_succ, programAll_append]
      cases programAll ((List.finRange done).flatMap fun index => requests index.val) oracle with
      | none => rfl
      | some updated =>
          simp only [Option.map_some, Option.bind_some]
          exact run' updated

/-- The request of limb `i`, by natural numbers. -/
def limbRequest (bits : BitInput) (star : Block) (answers : DesignatedLimbs) (limb : Nat) :
    List (Option BaseField × (Block × Block)) :=
  if inside : limb < limbCount .pointX then
    [(some (designatedInput bits ⟨limb, inside⟩ star), answers ⟨limb, inside⟩)]
  else []

omit [FieldCertificate] [DecidableEq PlanB.FixedIndex] [DecidableEq EncPRF.PermutationIndex] in
theorem limbHalf_low (answers : DesignatedLimbs) (limb : Nat) (bound : limb < limbCount .pointX) :
    limbHalf answers ⟨2 * limb, by omega⟩ = (answers ⟨limb, bound⟩).1 := by
  unfold limbHalf
  rw [if_pos (show 2 * limb % 2 = 0 by omega)]
  exact congrArg (fun index => (answers index).1) (Fin.ext (by dsimp only; omega))

omit [FieldCertificate] [DecidableEq PlanB.FixedIndex] [DecidableEq EncPRF.PermutationIndex] in
theorem limbHalf_high (answers : DesignatedLimbs) (limb : Nat) (bound : limb < limbCount .pointX) :
    limbHalf answers ⟨2 * limb + 1, by omega⟩ = (answers ⟨limb, bound⟩).2 := by
  unfold limbHalf
  rw [if_neg (show ¬ (2 * limb + 1) % 2 = 0 by omega)]
  exact congrArg (fun index => (answers index).2) (Fin.ext (by dsimp only; omega))

/-- **The `452` programs.** -/
theorem rsem_programs (bits : BitInput) (answers : DesignatedLimbs) (star : Block) (memory : Memory)
    (starCell : memory.ram (word designatedLabel) = blockWord star)
    (halves : ∀ half : Fin (2 * limbCount .pointX),
      memory.ram (word (halfCell half.val)) = blockWord (limbHalf answers half))
    (jCell : memory.ram (word tmpJStar) = word (designatedSwitch bits).val) :
    ∃ after, after.ram = memory.ram ∧ after.bits = memory.bits ∧ ∀ oracle,
      rsem Opening.programs memory oracle =
        PMF.pure ((programAll (programRequests bits (fun _ => some star) answers) oracle).map
          fun updated => (after, updated)) := by
  have step : ∀ limb inner, limb < limbCount .pointX → inner.ram = memory.ram →
      inner.bits = memory.bits → ∃ after, after.ram = memory.ram ∧ after.bits = memory.bits ∧
        ∀ oracle, rsem (Opening.programOne limb) inner oracle =
          PMF.pure ((programAll (limbRequest bits star answers limb) oracle).map
            fun updated => (after, updated)) := by
    intro limb inner bound ram bitsSame
    obtain ⟨after, afterRam, afterBits, run⟩ := rsem_programOne bits ⟨limb, bound⟩ inner star
      (answers ⟨limb, bound⟩).1 (answers ⟨limb, bound⟩).2 (by rw [ram, starCell])
      (by rw [ram, ← limbHalf_low answers limb bound]; exact halves ⟨2 * limb, by omega⟩)
      (by rw [ram, ← limbHalf_high answers limb bound]; exact halves ⟨2 * limb + 1, by omega⟩)
      (by rw [ram, jCell])
    refine ⟨after, afterRam.trans ram, afterBits.trans bitsSame, fun oracle => ?_⟩
    rw [run oracle]
    unfold limbRequest
    rw [dif_pos bound, programAll_single]
  obtain ⟨after, afterRam, afterBits, run⟩ := rsem_rep_programs (limbCount .pointX)
    Opening.programOne (limbRequest bits star answers) memory.ram memory.bits step
    (limbCount .pointX) memory le_rfl rfl rfl
  have lists : ((List.finRange (limbCount .pointX)).flatMap fun limb =>
      limbRequest bits star answers limb.val) = programRequests bits (fun _ => some star) answers := by
    unfold programRequests
    rw [List.map_eq_flatMap]
    refine congrArg (fun request => (List.finRange (limbCount .pointX)).flatMap request)
      (funext fun limb => ?_)
    unfold limbRequest
    rw [dif_pos limb.isLt]
    rfl
  refine ⟨after, afterRam, afterBits, fun oracle => ?_⟩
  rw [show Opening.programs = Prog.rep (limbCount .pointX) Opening.programOne from rfl, run oracle,
    lists]

/-! ### The opening, split -/

omit [FieldCertificate] [DecidableEq PlanB.FixedIndex] [DecidableEq EncPRF.PermutationIndex] in
/-- `openingFree` makes no oracle call. -/
theorem openingFree_noOracle : openingFree.NoOracle := by
  unfold openingFree
  simp only [Prog.seqList]
  have curveRoot (source : Register) : (Opening.curveRoot source).NoOracle := by
    unfold Opening.curveRoot
    simp only [Prog.seqList]
    exact ⟨rfl, rfl, rfl, rfl, rfl, noOracle_rep _ _ (fun _ _ => by
      unfold Opening.sqrtRound
      exact ⟨rfl, by split <;> first | rfl | trivial⟩), trivial⟩
  have betaMul : Opening.betaMul.NoOracle := by
    unfold Opening.betaMul Opening.copyPoint Opening.clearP
    simp only [Prog.seqList]
    exact ⟨⟨rfl, rfl, rfl, trivial⟩, ⟨rfl, rfl, rfl, trivial⟩, noOracle_rep _ _ (fun _ _ => by
      unfold Opening.betaRound
      exact ⟨rfl, by split <;> first | rfl | trivial⟩), trivial⟩
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, BigInt.noOracle_preimageSampler _ _ _ _ _, trivial⟩
  · exact noOracle_rep _ _ fun _ _ => by
      unfold Opening.tailOne
      simp only [Prog.seqList]
      refine ⟨noOracle_bounded _ _ _ _ ?_ ?_, noOracle_zeroRegs _, trivial⟩
      · unfold Opening.testCurveX
        simp only [Prog.seqList]
        exact ⟨rfl, rfl, curveRoot _, rfl, rfl, rfl, rfl, rfl, trivial⟩
      · unfold Opening.storeCurvePoint
        simp only [Prog.seqList]
        exact ⟨curveRoot _, ⟨rfl, trivial⟩, rfl, rfl, rfl, rfl, rfl, rfl, ⟨rfl, rfl⟩, ⟨rfl, rfl⟩,
          ⟨rfl, rfl⟩, trivial⟩
  · unfold Opening.horner Opening.clearP Opening.head Opening.storePoint
    simp only [Prog.seqList]
    exact ⟨⟨rfl, rfl, rfl, trivial⟩, noOracle_rep _ _ (fun _ _ => by
        unfold Opening.hornerStep Opening.loadPoint
        simp only [Prog.seqList]
        exact ⟨betaMul, ⟨⟨rfl, rfl⟩, ⟨rfl, rfl⟩, ⟨rfl, rfl⟩, trivial⟩, rfl, trivial⟩),
      ⟨betaMul, ⟨⟨rfl, rfl, ⟨rfl, rfl⟩, ⟨rfl, rfl⟩, ⟨rfl, rfl⟩, rfl,
        ⟨⟨rfl, rfl⟩, ⟨rfl, rfl⟩, ⟨rfl, rfl⟩, trivial⟩, noOracle_zeroRegs _, trivial⟩, trivial⟩,
        trivial⟩, trivial⟩
  · exact noOracle_rep _ _ fun _ _ =>
      ⟨noOracle_bounded _ _ _ _ ⟨rfl, rfl, rfl, rfl⟩ ⟨rfl, rfl⟩, noOracle_zeroRegs _⟩
  · exact noOracle_rep _ _ fun _ _ => by
      unfold Opening.liftOne Opening.loadPoint
      simp only [Prog.seqList]
      exact ⟨⟨rfl, rfl⟩, rfl, rfl, ⟨⟨rfl, rfl⟩, ⟨rfl, rfl⟩, ⟨rfl, rfl⟩, trivial⟩, rfl, rfl, rfl,
        rfl, rfl, rfl, rfl, rfl, rfl, rfl, ⟨rfl, rfl⟩, ⟨rfl, rfl⟩, ⟨rfl, rfl⟩,
        noOracle_zeroRegs _, trivial⟩
  · exact noOracle_rep _ _ fun _ _ =>
      ⟨⟨noOracle_bounded _ _ _ _ ⟨rfl, rfl⟩ (plain_storeNonCollector _).noOracle, noOracle_zeroRegs _⟩,
        ⟨noOracle_bounded _ _ _ _ ⟨rfl, rfl⟩ (plain_storeNonCollector _).noOracle, noOracle_zeroRegs _⟩⟩
  · exact noOracle_rep _ _ fun _ _ => by
      unfold Opening.solveDigit Opening.addScaled Opening.addCell Opening.finishTarget
        Opening.finishScaled
      simp only [Prog.seqList]
      exact ⟨⟨rfl, rfl⟩, ⟨rfl, rfl⟩, rfl, rfl, rfl, ⟨rfl, rfl⟩,
        ⟨rfl, rfl⟩, ⟨⟨rfl, rfl⟩, rfl, rfl, trivial⟩, ⟨⟨rfl, rfl⟩, rfl, rfl, trivial⟩,
        ⟨⟨rfl, rfl⟩, rfl, rfl, trivial⟩, ⟨⟨rfl, rfl⟩, rfl, rfl, trivial⟩, ⟨⟨rfl, rfl⟩, rfl, trivial⟩,
        ⟨⟨rfl, rfl⟩, rfl, trivial⟩, ⟨⟨rfl, rfl⟩, rfl, rfl, ⟨rfl, rfl⟩, trivial⟩,
        ⟨rfl, rfl⟩, ⟨⟨rfl, rfl⟩, rfl, rfl, trivial⟩, ⟨⟨rfl, rfl⟩, rfl, rfl, trivial⟩,
        ⟨⟨rfl, rfl⟩, rfl, rfl, trivial⟩, ⟨⟨rfl, rfl⟩, rfl, rfl, trivial⟩,
        ⟨⟨rfl, rfl⟩, rfl, rfl, trivial⟩, ⟨⟨rfl, rfl⟩, rfl, rfl, trivial⟩,
        ⟨⟨rfl, rfl⟩, rfl, rfl, trivial⟩, ⟨⟨rfl, rfl⟩, rfl, trivial⟩,
        ⟨⟨rfl, rfl⟩, rfl, rfl, rfl, rfl, ⟨rfl, rfl⟩, trivial⟩,
        ⟨rfl, rfl⟩, ⟨⟨rfl, rfl⟩, rfl, rfl, trivial⟩, ⟨⟨rfl, rfl⟩, rfl, trivial⟩,
        ⟨⟨rfl, rfl⟩, rfl, rfl, ⟨rfl, rfl⟩, trivial⟩, noOracle_zeroRegs _, trivial⟩

omit [DecidableEq PlanB.FixedIndex] [DecidableEq EncPRF.PermutationIndex] in
theorem rtree_zeroRegs (registers : List Register) (memory : Memory) :
    ∃ after, rtree (zeroRegs registers) memory = .pure (some after) ∧ after.ram = memory.ram ∧
      after.bits = memory.bits := by
  induction registers generalizing memory with
  | nil => exact ⟨memory, rfl, rfl, rfl⟩
  | cons register rest ih =>
      obtain ⟨after, run, ram, bitsSame⟩ := ih (setReg memory register (word 0))
      exact ⟨after, by rw [zeroRegs, rtree_cst_seq, run], ram, bitsSame⟩

omit [FieldCertificate] [DecidableEq PlanB.FixedIndex] [DecidableEq EncPRF.PermutationIndex] in
theorem zeroRegs_treeOps (registers : List Register) : (zeroRegs registers).OpsSatisfy TreeOp := by
  induction registers with
  | nil => trivial
  | cons register rest ih => exact ⟨trivial, ih⟩

/-- **The opening, split**: the oracle-free part, then the batch and the register clear. -/
theorem rsem_opening (memory : Memory) (oracle : OState PlanB.FixedIndex EncPRF.PermutationIndex) :
    rsem Opening.program memory oracle =
      (openingFree.memSem memory).bind fun result => match result with
        | none => PMF.pure none
        | some next => rsem (Prog.seqList [Opening.programs, zeroRegs allRegisters]) next
            oracle := by
  have free : rsem openingFree memory oracle =
      (openingFree.memSem memory).map (Option.map fun next => (next, oracle)) :=
    @sem_noOracle _ PlanB.FixedIndex EncPRF.PermutationIndex (Fintype.ofFinite _)
      (Fintype.ofFinite _) _ _ openingFree openingFree_noOracle memory oracle
  rw [show Opening.program = Prog.seqList ([Opening.tail, Opening.horner, Opening.lambdas,
      Opening.lifts, Opening.nonCollectors, Opening.solve, Opening.preimage] ++
      [Opening.programs, zeroRegs allRegisters]) from rfl, rsem_seqList_append,
    show Prog.seqList [Opening.tail, Opening.horner, Opening.lambdas, Opening.lifts,
      Opening.nonCollectors, Opening.solve, Opening.preimage] = openingFree from rfl]
  unfold andThen
  rw [free, PMF.bind_map]
  congr 1
  funext result
  cases result <;> rfl

/-- **The batch and the register clear.** -/
theorem rsem_programsTail (bits : BitInput) (answers : DesignatedLimbs) (star : Block)
    (memory : Memory) (starCell : memory.ram (word designatedLabel) = blockWord star)
    (halves : ∀ half : Fin (2 * limbCount .pointX),
      memory.ram (word (halfCell half.val)) = blockWord (limbHalf answers half))
    (jCell : memory.ram (word tmpJStar) = word (designatedSwitch bits).val) :
    ∃ after, after.ram = memory.ram ∧ after.bits = memory.bits ∧ ∀ oracle,
      rsem (Prog.seqList [Opening.programs, zeroRegs allRegisters]) memory oracle =
        PMF.pure ((programAll (programRequests bits (fun _ => some star) answers) oracle).map
          fun updated => (after, updated)) := by
  obtain ⟨middle, middleRam, middleBits, run⟩ :=
    rsem_programs bits answers star memory starCell halves jCell
  obtain ⟨after, runZero, afterRam, afterBits⟩ := rtree_zeroRegs allRegisters middle
  refine ⟨after, afterRam.trans middleRam, afterBits.trans middleBits, fun oracle => ?_⟩
  simp only [Prog.seqList]
  rw [rsem_seq]
  unfold andThen
  rw [run oracle, PMF.pure_bind]
  cases programAll (programRequests bits (fun _ => some star) answers) oracle with
  | none => rfl
  | some updated =>
      simp only [Option.map_some]
      rw [rsem_seq_skip, rsem_of_tree _ (zeroRegs_treeOps _) _ _ runZero updated]

end

end Kriterion.ArgoMAC.PlanB.SimMachine
