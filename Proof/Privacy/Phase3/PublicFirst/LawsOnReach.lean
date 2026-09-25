/-
**Phase 3, P1o — toward `LawOn`: on the curve, the reach asks only planted questions and fresh
gadget ones.**

`LawOn`'s upper side runs the designed shadow (`shadowOnM`: the prefix again, the bit-`true` pads,
the whole evaluator) lazily on the garbler's EncPRF and designed entries planted on the empty
oracle. Its first reduction (`runLazyQ_eager`, then planting) needs to know which of the shadow's
questions are already planted. This file proves the classification on the curve
(`onCurve_reach_classified`): every question of the evaluator on `u`'s labels, run on the tape, is

* the question of one of the garbler's EncPRF or designed entries (`upperEntries`), or
* a gadget question of a digit without exceptional input: the only fresh questions (the garbler
  asks both bits of every position of every other digit, at the transformed labels, and the reach
  asks the index of `u`'s bit at the same label).

The garbler side (`asks_garbleM_*`: the garbler asks every gate of every paid fold level of every
chunk, at every chunk width, every limb of every switch, the bridge hash at `bridgeInput t`, both
EncPRF pads of every position and both bits of every gadget position of every digit with an
exceptional input, at its own points) is the converse of `garblerTranscript_good`; the reach side is `onCurveM_asks`
(`LawsGuessReach`) with the evaluator-correctness lemmas of the hidden hop (`evalFold_off`: at every
level the evaluator's labels off the active parent are the garbler's).
-/

import Proof.Privacy.Phase3.PublicFirst.LawsGuess

set_option linter.unusedSectionVars false
set_option maxRecDepth 8000
set_option autoImplicit false

namespace Kriterion.ArgoMAC.Security.Phase3.PublicFirst.OnReach

open BN254 Cryptography GarbledCircuit Kriterion.ArgoMAC.PlanB
open Kriterion.ArgoMAC.Scheme (Coins Oracle)
open Kriterion.ArgoMAC.Security.Phase3.Hidden (transcriptOf QueryOnly)
open Kriterion.ArgoMAC.Security.Phase3.PublicFirst.Guess
open Kriterion.ArgoMAC.Phase3.Lazy (cellInput)

noncomputable section

/-! ### 1. Asked questions through binds with known values and through `pi` -/

theorem asks_bind_eq {α β : Type} {ans : ∀ q : PublicQuery FixedIndex EncPRF.PermutationIndex, q.Answer}
    {P : FreeQuery Programs.Spec α} {f : α → FreeQuery Programs.Spec β}
    {q : PublicQuery FixedIndex EncPRF.PermutationIndex} (value : α) (evalEq : P.eval ans = value)
    (asks : Asks ans (f value) q) : Asks ans (P >>= f) q := by
  subst evalEq
  exact Asks.bind_right asks

theorem asks_pi {ans : ∀ q : PublicQuery FixedIndex EncPRF.PermutationIndex, q.Answer}
    {q : PublicQuery FixedIndex EncPRF.PermutationIndex} : ∀ (count : Nat) {γ : Fin count → Type}
    {P : (index : Fin count) → FreeQuery Programs.Spec (γ index)} (i : Fin count),
    Asks ans (P i) q → Asks ans (FreeQuery.pi count P) q
  | 0, _, _, i, _ => i.elim0
  | count + 1, _, P, i, asks => by
      show Asks ans (P 0 >>= fun head => FreeQuery.pi count (fun index => P index.succ) >>= fun tail =>
        Pure.pure (Fin.cons head tail)) q
      by_cases zero : i = 0
      · subst zero
        exact Asks.bind_left asks
      · obtain ⟨j, rfl⟩ := Fin.exists_succ_eq.mpr zero
        exact Asks.bind_right (Asks.bind_left (asks_pi count (P := fun index => P index.succ) j asks))

/-! ### 2. The garbler asks its own questions -/

section Garbler

variable [FieldCertificate] [GroupCertificate]

/-- The fold of more than `n` levels asks every gate of level `n ≥ 1` at the garbler's level-`n`
label. -/
theorem asks_garbleFoldM (O : Oracle) (lane : Lane) (c : Fin chunkCount) (delta : Block)
    (zeroLabel : Nat → Block) (n : Nat) (one : 1 ≤ n) (r : Fin (2 ^ n)) (half : Bool) :
    ∀ steps, n + 1 ≤ steps →
      Asks (publicAnswer O) (Programs.garbleFoldM lane c delta zeroLabel steps)
        (.fixedForward (hotIndexNat lane c n r.val half) ((garbleFold O.1 lane c delta zeroLabel n).1 r))
  | 0, small => absurd small (by omega)
  | steps + 1, small => by
      show Asks _ (Programs.garbleFoldM lane c delta zeroLabel steps >>= fun previous =>
        Programs.garbleStepM lane c steps (zeroLabel steps) previous.1 >>= fun right =>
          Pure.pure (extendLevel steps previous.1 right,
            fun step => if step = steps then stepJoin steps (zeroLabel steps) right
              else previous.2 step)) _
      by_cases last : steps = n
      · subst last
        refine asks_bind_eq _ (Programs.eval_garbleFoldM O lane c delta zeroLabel steps)
          (Asks.bind_left ?_)
        unfold Programs.garbleStepM
        rw [if_neg (by omega)]
        refine Asks.bind_left (Asks.vector _ r ?_)
        unfold Programs.foldMaskM
        cases half
        · exact Asks.bind_left (Asks.hashM _ _)
        · exact Asks.bind_right (Asks.bind_left (Asks.hashM _ _))
      · exact Asks.bind_left (asks_garbleFoldM O lane c delta zeroLabel n one r half steps (by omega))

/-- **A lane of the garbler asks every gate of every paid fold level** at its label. -/
theorem asks_laneM_hot (O : Oracle) (lane : Lane) (delta : Block)
    (bitKey : Fin PlanB.coordinateBits → Block × Block) (c : Fin chunkCount) (n : Nat)
    (one : 1 ≤ n) (small : n < chunkWidth c) (r : Fin (2 ^ n)) (half : Bool) :
    Asks (publicAnswer O) (Programs.laneM lane delta bitKey)
      (.fixedForward (hotIndexNat lane c n r.val half)
        ((garbleFold O.1 lane c delta (labelAt fun p => (chunkKey bitKey c p).1) n).1 r)) := by
  unfold Programs.laneM
  refine Asks.bind_left (asks_pi _ c ?_)
  unfold Programs.chunkTablesM Programs.garbleChunkM
  exact Asks.bind_left (Asks.bind_left (asks_garbleFoldM O lane c delta _ n one r half
    (chunkWidth c) small))

/-- **A lane of the garbler asks every limb of every switch** at its one-hot label. -/
theorem asks_laneM_cell (O : Oracle) (lane : Lane) (delta : Block)
    (bitKey : Fin PlanB.coordinateBits → Block × Block) (c : Fin chunkCount)
    (j : Fin (2 ^ chunkWidth c)) (limb : Fin (limbCount lane)) :
    Asks (publicAnswer O) (Programs.laneM lane delta bitKey)
      (.hash (cellInput ⟨⟨lane, c, j⟩, limb⟩ ((garbleChunk O.1 lane delta bitKey c).1 j))) := by
  unfold Programs.laneM
  refine Asks.bind_left (asks_pi _ c ?_)
  unfold Programs.chunkTablesM
  refine asks_bind_eq _ (Programs.eval_garbleChunkM O lane delta bitKey c)
    (Asks.bind_left (Asks.vector _ j ?_))
  exact asks_switchMaskM O lane c j.val _ limb

/-- The garbler's pads ask both bits of every position. -/
theorem asks_padsM (O : Oracle) (keys : WhiteningKeys) (coordinate : EncPRF.Coordinate)
    (index : Fin coordinateBitCount) (bit : Bool) :
    Asks (publicAnswer O) (Programs.padsM keys) (.encForward (coordinate, index) (encodeBit bit ^^^ keys.first)) := by
  have pad : Asks (publicAnswer O) (Programs.padM keys coordinate index bit)
      (.encForward (coordinate, index) (encodeBit bit ^^^ keys.first)) := Asks.bind_left (Asks.ask' _)
  have row : Asks (publicAnswer O) (FreeQuery.vector coordinateBitCount fun index =>
      Programs.padM keys coordinate index false >>= fun zero =>
        Programs.padM keys coordinate index true >>= fun one => Pure.pure (zero, one))
      (.encForward (coordinate, index) (encodeBit bit ^^^ keys.first)) := by
    refine Asks.vector _ index ?_
    cases bit
    · exact Asks.bind_left pad
    · exact Asks.bind_right (Asks.bind_left pad)
  unfold Programs.padsM
  cases coordinate
  · exact Asks.bind_left row
  · exact Asks.bind_right (Asks.bind_left row)

/-- The garbler's pairs ask both bits of every position, at the bits' labels. -/
theorem asks_gadgetPairsM (ans : ∀ q : PublicQuery FixedIndex EncPRF.PermutationIndex, q.Answer)
    (o : Fin digitCount) (coordinate : EncPRF.Coordinate) (key : CoordinateMacKey)
    (position : Fin PlanB.coordinateBits) (bit : Bool) :
    Asks ans (Programs.gadgetPairsM o coordinate key)
      (.fixedForward (.gadget o (Pipeline.gadgetCoord coordinate) position bit)
        (BitAdaptor.encode key[position.val] bit)) := by
  unfold Programs.gadgetPairsM
  refine Asks.vector _ position ?_
  cases bit
  · exact Asks.bind_left (Asks.hashM _ _)
  · exact Asks.bind_right (Asks.bind_left (Asks.hashM _ _))

/-- The gadget of a digit with an exceptional input asks both bits of every position, at their
labels. -/
theorem asks_gadgetM (ans : ∀ q : PublicQuery FixedIndex EncPRF.PermutationIndex, q.Answer)
    (keys : FieldMacToECMac.OutputKeys) (inputKey : InputMacKey)
    (pads : FieldMacToECMac.ExceptionPad) (o : Fin digitCount) (κ : Coord) (position : Fin PlanB.coordinateBits)
    (bit : Bool) (phi : BaseField) (found : digitEndomorphismBase (keys.get o).digit = some phi) :
    Asks ans (Programs.gadgetM keys inputKey pads)
      (.fixedForward (.gadget o κ position bit) (BitAdaptor.encode (keyAt inputKey κ position) bit)) := by
  unfold Programs.gadgetM
  refine Asks.vector _ o ?_
  unfold Programs.garbleEntryM
  rw [found]
  cases κ
  · exact Asks.bind_left (asks_gadgetPairsM ans o .x _ position bit)
  · exact Asks.bind_right (Asks.bind_left (asks_gadgetPairsM ans o .y _ position bit))

/-- **The garbler asks every question of each of its lanes.** -/
theorem asks_garbleM_lane (scalar : NonZeroScalar) (tape : Coins × Oracle) (lane : Lane)
    {q : PublicQuery FixedIndex EncPRF.PermutationIndex}
    (asks : Asks (publicAnswer tape.2) (Programs.laneM lane ((Hidden.laneKeys tape).1 lane)
      ((Hidden.laneKeys tape).2 lane)) q) :
    Asks (publicAnswer tape.2) (Programs.garbleM scalar tape.1) q := by
  unfold Programs.garbleM
  refine asks_bind_eq (tape.2.2.2 (bridgeInput tape.1.bridgeKey)) (Programs.eval_askHash _ _) ?_
  refine asks_bind_eq _ (Programs.eval_padsM _ _) ?_
  cases lane
  · exact Asks.bind_left asks
  · exact Asks.bind_right (Asks.bind_left asks)
  · exact Asks.bind_right (Asks.bind_right (Asks.bind_left asks))
  · exact Asks.bind_right (Asks.bind_right (Asks.bind_right (Asks.bind_left asks)))

theorem asks_garbleM_hash (scalar : NonZeroScalar) (tape : Coins × Oracle) :
    Asks (publicAnswer tape.2) (Programs.garbleM scalar tape.1) (.hash (bridgeInput tape.1.bridgeKey)) := by
  unfold Programs.garbleM
  exact Asks.bind_left (Asks.ask' _)

theorem asks_garbleM_enc (scalar : NonZeroScalar) (tape : Coins × Oracle) (coordinate : EncPRF.Coordinate)
    (index : Fin coordinateBitCount) (bit : Bool) :
    Asks (publicAnswer tape.2) (Programs.garbleM scalar tape.1)
      (.encForward (coordinate, index)
        (encodeBit bit ^^^ (tape.2.2.2 (bridgeInput tape.1.bridgeKey)).1)) := by
  unfold Programs.garbleM
  refine asks_bind_eq (tape.2.2.2 (bridgeInput tape.1.bridgeKey)) (Programs.eval_askHash _ _)
    (Asks.bind_left ?_)
  exact asks_padsM tape.2 ⟨(tape.2.2.2 (bridgeInput tape.1.bridgeKey)).1,
    (tape.2.2.2 (bridgeInput tape.1.bridgeKey)).2⟩ coordinate index bit

/-- **The garbler asks both bits of every gadget position of every digit with an exceptional
input**, at their labels. -/
theorem asks_garbleM_gadget (scalar : NonZeroScalar) (tape : Coins × Oracle) (o : Fin digitCount) (κ : Coord)
    (position : Fin PlanB.coordinateBits) (bit : Bool)
    (some : (digitEndomorphismBase (Hidden.digitKey scalar tape.1.offsets o).digit).isSome = true) :
    Asks (publicAnswer tape.2) (Programs.garbleM scalar tape.1)
      (.fixedForward (.gadget o κ position bit) (Hidden.gadgetLabel scalar tape o κ position bit)) := by
  obtain ⟨phi, found⟩ := Option.isSome_iff_exists.mp some
  have asks := asks_gadgetM (publicAnswer tape.2) (FieldMacToECMac.outputKeys construction scalar.value tape.1.offsets)
    (Programs.transformKeyOf (Programs.realPads tape.2.2.1
      ⟨(tape.2.2.2 (bridgeInput tape.1.bridgeKey)).1, (tape.2.2.2 (bridgeInput tape.1.bridgeKey)).2⟩)
        tape.1.inputMacKey)
    tape.1.exceptionPad o κ position bit phi found
  have label : Hidden.gadgetLabel scalar tape o κ position bit =
      BitAdaptor.encode (keyAt (Programs.transformKeyOf (Programs.realPads tape.2.2.1
        ⟨(tape.2.2.2 (bridgeInput tape.1.bridgeKey)).1, (tape.2.2.2 (bridgeInput tape.1.bridgeKey)).2⟩)
          tape.1.inputMacKey) κ position) bit := by
    unfold Hidden.gadgetLabel
    rw [found]
    dsimp only
    rw [← Programs.transformKeyOf_realPads]
    cases κ
    · exact rfl
    · exact rfl
  rw [label]
  unfold Programs.garbleM
  refine asks_bind_eq (tape.2.2.2 (bridgeInput tape.1.bridgeKey)) (Programs.eval_askHash _ _) ?_
  refine asks_bind_eq _ (Programs.eval_padsM _ _) ?_
  exact Asks.bind_right (Asks.bind_right (Asks.bind_right (Asks.bind_right (Asks.bind_left asks))))

/-! ### 3. On the curve, the reach's labels are the garbler's off the active entries -/

/-- On the curve the reach's labels are the garbler's lane keys selected by `u`'s bits. -/
theorem laneLabels_onCurve (tape : Coins × Oracle) (input : AffineInput) (valid : validate input = true)
    (lane : Lane) :
    laneLabels tape input lane = selectBits ((Hidden.laneKeys tape).2 lane) (inputBits input lane.coord) := by
  have key := evalKey_eq tape.1 input valid
  cases lane
  · exact macLabels_raw tape.1.inputMacKey input .x
  · exact macLabels_raw tape.1.inputMacKey input .y
  · exact macLabels_white tape input .x _ key
  · exact macLabels_white tape input .y _ key

theorem lanePub_garble (parameter : ℕ) (scalar : NonZeroScalar) (tape : Coins × Oracle) (lane : Lane) :
    lanePub (Scheme.scheme.garble parameter scalar tape).1 lane =
      hotJoins tape.2.1 lane ((Hidden.laneKeys tape).1 lane) ((Hidden.laneKeys tape).2 lane) := by
  rw [garble_table]
  cases lane <;> rfl

/-- **On the curve the reach's labels at every level off the active parent are the garbler's.** -/
theorem reachFold_onCurve (parameter : ℕ) (scalar : NonZeroScalar) (tape : Coins × Oracle)
    (input : AffineInput) (valid : validate input = true) (lane : Lane) (c : Fin chunkCount)
    (n : Nat) (small : n ≤ chunkWidth c) (r : Fin (2 ^ n))
    (off : r ≠ activeAt (chunkValue (inputBits input lane.coord) c).toNat n) :
    reachFold parameter scalar tape input lane c n r = garbFold tape lane c n r := by
  unfold reachFold garbFold
  rw [laneLabels_onCurve tape input valid, lanePub_garble]
  refine evalFold_off tape.2.1 lane _ _ (laneKeys_correlated tape lane) _ c n small r ?_
  intro same
  apply off
  apply Fin.ext
  show r.val = (chunkValue (inputBits input lane.coord) c).toNat % 2 ^ n
  rw [chunkValue_toNat]
  exact same

/-- **On the curve the reach's one-hot labels off the active switch are the garbler's.** -/
theorem reachFold_two_onCurve (parameter : ℕ) (scalar : NonZeroScalar) (tape : Coins × Oracle)
    (input : AffineInput) (valid : validate input = true) (lane : Lane) (c : Fin chunkCount)
    (j : Fin (2 ^ chunkWidth c)) (off : j ≠ chunkOf (inputBits input lane.coord) c) :
    reachFold parameter scalar tape input lane c (chunkWidth c) j =
      (garbleChunk tape.2.1 lane ((Hidden.laneKeys tape).1 lane) ((Hidden.laneKeys tape).2 lane) c).1 j := by
  unfold reachFold
  rw [laneLabels_onCurve tape input valid, lanePub_garble]
  show evalHot tape.2.1 lane c (chunkWidth c)
    (hotSlice (hotJoins tape.2.1 lane ((Hidden.laneKeys tape).1 lane) ((Hidden.laneKeys tape).2 lane)) c)
    (chunkLabels (selectBits ((Hidden.laneKeys tape).2 lane) (inputBits input lane.coord)) c)
    (chunkValue (inputBits input lane.coord) c) j = _
  rw [hotSlice_hotJoins, chunkLabels_selectBits]
  exact evalHot_agrees_off_active (laneKeys_correlated tape lane) _ c j off

/-! ### 4. The classification -/

/-- A garbler question is the question of a garbler transcript entry. -/
theorem entry_of_asks (scalar : NonZeroScalar) (tape : Coins × Oracle)
    {q : PublicQuery FixedIndex EncPRF.PermutationIndex}
    (asks : Asks (publicAnswer tape.2) (Programs.garbleM scalar tape.1) q) :
    ∃ e ∈ garblerTranscript scalar tape, e.1 = q := by
  unfold Asks at asks
  rw [← garblerTranscript_eq] at asks
  exact List.mem_map.mp asks

/-- A designed garbler entry is planted on the upper side. -/
theorem upper_of_designed (parameter : ℕ) (scalar : NonZeroScalar) (tape : Coins × Oracle)
    (input : AffineInput) (e : Entry FixedIndex EncPRF.PermutationIndex)
    (member : e ∈ garblerTranscript scalar tape) (plain : e.IsEnc = false)
    (designed : designedRule scalar tape input e = true) : e ∈ upperEntries parameter scalar tape input := by
  unfold upperEntries designedInstall
  exact List.mem_append_right _ (List.mem_filter.mpr ⟨member, by simp [plain, designed]⟩)

/-- A garbler EncPRF entry is planted on the upper side. -/
theorem upper_of_enc (parameter : ℕ) (scalar : NonZeroScalar) (tape : Coins × Oracle)
    (input : AffineInput) (e : Entry FixedIndex EncPRF.PermutationIndex)
    (member : e ∈ garblerTranscript scalar tape) (enc : e.IsEnc = true) :
    e ∈ upperEntries parameter scalar tape input := by
  unfold upperEntries encEntries
  exact List.mem_append_left _ (List.mem_filter.mpr ⟨member, enc⟩)

/-- A planted designed question at a fixed index. -/
theorem upper_of_fixed (parameter : ℕ) (scalar : NonZeroScalar) (tape : Coins × Oracle)
    (input : AffineInput) (index : FixedIndex) (x : Block)
    (asks : Asks (publicAnswer tape.2) (Programs.garbleM scalar tape.1) (.fixedForward index x))
    (designed : designedIndex scalar tape input index = true) :
    ∃ e ∈ upperEntries parameter scalar tape input, e.1 = .fixedForward index x := by
  obtain ⟨e, member, eq⟩ := entry_of_asks scalar tape asks
  refine ⟨e, upper_of_designed parameter scalar tape input e member ?_ ?_, eq⟩
  · obtain ⟨request, answer⟩ := e
    simp only at eq
    subst eq
    rfl
  · obtain ⟨request, answer⟩ := e
    simp only at eq
    subst eq
    exact designed

/-- A planted designed hash question. -/
theorem upper_of_hash (parameter : ℕ) (scalar : NonZeroScalar) (tape : Coins × Oracle)
    (input : AffineInput) (key : BaseField)
    (asks : Asks (publicAnswer tape.2) (Programs.garbleM scalar tape.1) (.hash key))
    (designed : designedHash input key = true) :
    ∃ e ∈ upperEntries parameter scalar tape input, e.1 = .hash key := by
  obtain ⟨e, member, eq⟩ := entry_of_asks scalar tape asks
  refine ⟨e, upper_of_designed parameter scalar tape input e member ?_ ?_, eq⟩
  · obtain ⟨request, answer⟩ := e
    simp only at eq
    subst eq
    rfl
  · obtain ⟨request, answer⟩ := e
    simp only at eq
    subst eq
    exact designed

/-- A lane question of the reach on the curve is planted. -/
theorem lane_planted (parameter : ℕ) (scalar : NonZeroScalar) (tape : Coins × Oracle)
    (input : AffineInput) (valid : validate input = true) (lane : Lane)
    (q : PublicQuery FixedIndex EncPRF.PermutationIndex)
    (ask : LaneAsk tape.2.1 lane (lanePub (Scheme.scheme.garble parameter scalar tape).1 lane)
      (inputBits input lane.coord) (laneLabels tape input lane) q) :
    ∃ e ∈ upperEntries parameter scalar tape input, e.1 = q := by
  obtain ⟨c, ⟨n, r, half, small, off, rfl⟩ | ⟨j, limb, off, rfl⟩⟩ := ask
  · have one : 1 ≤ n := by
      rcases Nat.lt_or_ge n 1 with zero | one
      · obtain rfl : n = 0 := by omega
        exact absurd (activeAt_zero _ r) off
      · exact one
    have point := reachFold_onCurve parameter scalar tape input valid lane c n small.le r off
    refine upper_of_fixed parameter scalar tape input _ _ ?_ ?_
    · show Asks _ _ (.fixedForward (hotIndexNat lane c n r.val half)
        (reachFold parameter scalar tape input lane c n r))
      rw [point]
      exact asks_garbleM_lane scalar tape lane (asks_laneM_hot tape.2 lane _ _ c n one small r half)
    · have offNat : r.val ≠ (chunkOf (inputBits input lane.coord) c).val % 2 ^ n := by
        intro same
        apply off
        apply Fin.ext
        show r.val = (chunkValue (inputBits input lane.coord) c).toNat % 2 ^ n
        rw [chunkValue_toNat]
        exact same
      have nSmall : n < chunkBits := lt_of_lt_of_le small (chunkWidth_le c)
      have rSmall : r.val < 2 ^ chunkBits :=
        lt_of_lt_of_le r.isLt (Nat.pow_le_pow_right (by norm_num) nSmall.le)
      rw [hotIndexNat_eq lane c n r.val half nSmall rSmall]
      show (decide (r.val ≠ (chunkOf (inputBits input lane.coord) c).val % 2 ^ n) &&
        (laneIsCurve lane || validate input)) = true
      rw [decide_eq_true offNat, valid, Bool.or_true, Bool.and_true]
  · have point := reachFold_two_onCurve parameter scalar tape input valid lane c j off
    refine upper_of_hash parameter scalar tape input _ ?_ ?_
    · show Asks _ _ (.hash (cellInput ⟨⟨lane, c, j⟩, limb⟩
        (reachFold parameter scalar tape input lane c (chunkWidth c) j)))
      rw [point]
      exact asks_garbleM_lane scalar tape lane (asks_laneM_cell tape.2 lane _ _ c j limb)
    · refine (designedHash_labelInput input ⟨⟨lane, c, j⟩, limb⟩ _).trans ?_
      show (decide (j ≠ chunkOf (inputBits input lane.coord) c) &&
        (laneIsCurve lane || validate input)) = true
      rw [decide_eq_true off, valid, Bool.or_true, Bool.and_true]

/-- **On the curve, every question of the reach is planted on the upper side or a fresh gadget
question** (at an index where the garbler has no designed entry). -/
theorem onCurve_reach_classified (parameter : ℕ) (scalar : NonZeroScalar) (tape : Coins × Oracle)
    (input : AffineInput) (valid : validate input = true) (q : PublicQuery FixedIndex EncPRF.PermutationIndex)
    (reached : q ∈ (transcriptOf (publicAnswer tape.2)
      (Programs.onCurveM (Scheme.scheme.garble parameter scalar tape).1 (BitInput.ofAffine input)
        (macOf tape input))).map Sigma.fst) :
    (∃ e ∈ upperEntries parameter scalar tape input, e.1 = q) ∨
    (∃ (o : Fin digitCount) (κ : Coord) (position : Fin PlanB.coordinateBits),
      q = .fixedForward (.gadget o κ position ((inputBits input κ).getLsb position))
        (reachGadget tape input κ position) ∧
      ∀ e ∈ upperEntries parameter scalar tape input, ∀ x,
        e.1 ≠ .fixedForward (.gadget o κ position ((inputBits input κ).getLsb position)) x) := by
  obtain ⟨entry, entryMember, rfl⟩ := List.mem_map.mp reached
  have ask := onCurveM_asks tape.2 _ _ _ entry entryMember
  have pads := reachPads_eq parameter scalar tape input
  have hashArg := reach_hashArg parameter scalar tape input
  have key := evalKey_eq tape.1 input valid
  unfold ReachAsk at ask
  rw [pads] at ask
  rcases ask with a | a | a | a | a | a | a
  · exact Or.inl (lane_planted parameter scalar tape input valid .curveX _ a)
  · exact Or.inl (lane_planted parameter scalar tape input valid .curveY _ a)
  · left
    rw [a]
    have eq : reachHashArg tape.2 (Scheme.scheme.garble parameter scalar tape).1 (BitInput.ofAffine input)
        (macOf tape input) = tape.1.bridgeKey := hashArg.trans key
    rw [eq]
    exact upper_of_hash parameter scalar tape input _ (asks_garbleM_hash scalar tape)
      ((designedHash_bridgeInput input _).trans valid)
  · left
    obtain ⟨coordinate, index, bit, eq⟩ := a
    rw [eq]
    have keyEq : reachHashArg tape.2 (Scheme.scheme.garble parameter scalar tape).1 (BitInput.ofAffine input)
        (macOf tape input) = tape.1.bridgeKey := hashArg.trans key
    rw [keyEq]
    obtain ⟨e, member, eEq⟩ := entry_of_asks scalar tape (asks_garbleM_enc scalar tape coordinate index bit)
    refine ⟨e, upper_of_enc parameter scalar tape input e member ?_, eEq⟩
    obtain ⟨request, answer⟩ := e
    simp only at eEq
    subst eEq
    rfl
  · exact Or.inl (lane_planted parameter scalar tape input valid .pointX _ a)
  · exact Or.inl (lane_planted parameter scalar tape input valid .pointY _ a)
  · obtain ⟨o, κ, position, eq⟩ := a
    rw [BitInput.toAffineOfAffine] at eq
    rw [eq]
    by_cases planted : (digitEndomorphismBase (Hidden.digitKey scalar tape.1.offsets o).digit).isSome = true
    · left
      have label : macAt (Programs.transformMacOf (padsOf tape input) (macOf tape input)) κ position =
          Hidden.gadgetLabel scalar tape o κ position ((inputBits input κ).getLsb position) := by
        have onCurve := reachGadget_onCurve tape input valid κ position
        unfold reachGadget at onCurve
        rw [onCurve, gadgetLabel_eq scalar tape o κ position _ planted]
      rw [label]
      refine upper_of_fixed parameter scalar tape input _ _
        (asks_garbleM_gadget scalar tape o κ position _ planted) ?_
      show (validate input && decide ((inputBits input κ).getLsb position =
        (inputBits input κ).getLsb position)) = true
      rw [valid]
      simp
    · right
      refine ⟨o, κ, position, rfl, fun e member x same => ?_⟩
      unfold upperEntries at member
      rcases List.mem_append.mp member with enc | designed
      · unfold encEntries at enc
        have isEnc := (List.mem_filter.mp enc).2
        obtain ⟨request, answer⟩ := e
        simp only at same
        subst same
        simp [Entry.IsEnc] at isEnc
      · unfold designedInstall at designed
        obtain ⟨inGarbler, rule⟩ := List.mem_filter.mp designed
        have shape := garblerTranscript_ask scalar tape e inGarbler
        obtain ⟨request, answer⟩ := e
        simp only at same
        subst same
        have some : (digitEndomorphismBase (Hidden.digitKey scalar tape.1.offsets o).digit).isSome = true :=
          shape
        exact planted some

end Garbler

end

end Kriterion.ArgoMAC.Security.Phase3.PublicFirst.OnReach
