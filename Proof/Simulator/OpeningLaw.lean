/-
**The opening law** (`SimMachine.OpeningLaw`, stated in `Stage2Spec.lean`).

From every memory satisfying `OpeningPre`, the oracle-free opening `openingFree` (`tail, horner,
lambdas, lifts, nonCollectors, solve, preimage`) read through `openView` is P3's
`openingLimbs boundedSamplers …` read through `blocksView`:

1. the tail is `optionProduct 90 curvePointLaw` (`memSem_tail`), and Horner's head clamp aborts
   exactly on `tailLaw`'s check (`memSem_horner`), so tail + head is `boundedSamplers.tail`;
2. the randomisers are `boundedSamplers.lift` (`memSem_lambdas`), and the lifts are `targetRows`
   (`memSem_lifts`);
3. the non-collectors are `boundedSamplers.free` (`memSem_nonCollectors`; draw `2d + s` is the
   free coordinate `(d, s)`, `freeLaw`'s `finProdFinEquiv` order), and leave the accumulators at
   `freeFill` (`nc_value`);
4. the solve on the free-filled rows stores `collectorTargets` of `freeRows` in the collector
   cells (the `Y` collector's target times `(x · x)⁻¹`, the machine's `finishScaled` and the
   Glue's `collectorScale` alike), so the designated cells hold `solvedVector`
   (`designated_cells`, from T10a's `designatedVector_free` and `designatedVector_collector`);
5. the preimage sampler is `boundedSamplers.preimage (solvedVector …)` (`memSem_preimage`), and
   the half cells hold the drawn limbs' halves (`samplerFinal_half`, `halfValue_limbHalf`);
6. `tmpJStar`, `E*`, the labels and the stacks are unchanged throughout (`SameOff` off the
   non-collectors, `ncFold_off` across them).
-/

import Proof.Simulator.OpeningPreimage

namespace Kriterion.ArgoMAC.PlanB.SimMachine

open BN254 Cryptography Cryptography.BoundedMachine Blocks GarbledCircuit
open Kriterion.ArgoMAC.Phase3.Glue

noncomputable section

variable [FieldCertificate]

/-! ### Small facts -/

omit [FieldCertificate] in
theorem gammaConst_eq_rowField (row : RowGamma) : ∀ slot, gammaConst row slot = rowField row slot
  | 0 => rfl
  | 1 => rfl
  | 2 => rfl
  | 3 => rfl
  | 4 => rfl
  | 5 => rfl
  | 6 => rfl
  | 7 => rfl
  | 8 => rfl
  | 9 => rfl
  | 10 => rfl
  | _ + 11 => rfl

theorem readWords_outputWords (target : Point) : readWords (outputWords target) = some target := by
  cases target with
  | zero => rfl
  | some x y valid =>
      rw [← readWords_pointWords (.some x y valid)]
      rfl

omit [FieldCertificate] in
theorem labelVector_sameOff {before after : Word → Word} (same : SameOff before after) :
    labelVector after = labelVector before := by
  unfold labelVector
  congr 1
  funext index
  rw [same _ (not_openCell _ (by unfold labelBase openBase; omega))]

/-- A collector's word is the Glue's collector target: `κ · (W.c − row.c) · collectorScale`. -/
theorem solveWords_component (kappaValue : BaseField) (bits : BitInput)
    (target row : FieldMacToECMac.HomogeneousValue) (collector : Fin 3) :
    wordAt (solveWords kappaValue bits.toAffine.x target row) collector.val =
      fieldWord (kappaValue * (collectorComponent collector target -
        collectorComponent collector row) * collectorScale bits collector) := by
  fin_cases collector
  · show fieldWord _ = fieldWord (_ * (if (0 : Nat) = 1 then _ else 1))
    rw [if_neg (by decide), mul_one]
    rfl
  · show fieldWord _ = fieldWord (_ * (if (1 : Nat) = 1 then _ else 1))
    rw [if_pos rfl]
    rfl
  · show fieldWord _ = fieldWord (_ * (if (2 : Nat) = 1 then _ else 1))
    rw [if_neg (by decide), mul_one]
    rfl

/-! ### Across the non-collectors -/

/-- A cell below the accumulators is away from every non-collector. -/
theorem ncAway_low (index : Nat) (small : index < digitCount * 2) (address : Nat)
    (below : address < accBase) : NcAway (ncElement index) (word address) := by
  have element := ncElement_lt index small
  unfold accBase at below
  exact ⟨word_ne (by omega) (by addr_arith) (by addr_arith),
    word_ne (by omega) (by addr_arith) (by addr_arith)⟩

/-- A cell between the `pointX` accumulators and the designated cells is away from every
non-collector. -/
theorem ncAway_mid (index : Nat) (small : index < digitCount * 2) (address : Nat)
    (above : accBase + 455 ≤ address) (below : address < designatedBase) :
    NcAway (ncElement index) (word address) := by
  have element := ncElement_lt index small
  unfold accBase at above
  unfold designatedBase at below
  exact ⟨word_ne (by omega) (by addr_arith) (by addr_arith),
    word_ne (by omega) (by addr_arith) (by addr_arith)⟩

theorem labelVector_nc (count : Nat) (fits : count ≤ digitCount * 2) (memory : Memory)
    (values : Fin count → BaseField) :
    labelVector (foldStore (ncStep 0) count memory values).ram = labelVector memory.ram := by
  unfold labelVector
  congr 1
  funext index
  rw [ncFold_off count 0 memory values _ (fun later bound =>
    ncAway_low (later + 0) (by omega) _ (by unfold labelBase accBase; omega))]

/-- The free coordinates of the draws, in `freeLaw`'s order. -/
def freeOf (draws : Fin (digitCount * 2) → BaseField) : FreeSite → BaseField :=
  fun site => draws (finProdFinEquiv site)

omit [FieldCertificate] in
theorem finProdFinEquiv_free (digit : Fin digitCount) (slot : Fin 2) :
    (finProdFinEquiv (digit, slot)).val = 2 * digit.val + slot.val := by
  rw [finProdFinEquiv_apply_val]
  dsimp only
  omega

/-- **The accumulators after the non-collectors**: each `pointX` value plus `κ` times the
designated vector's free part. -/
theorem nc_value (memory : Memory) (draws : Fin (digitCount * 2) → BaseField)
    (digit : Fin digitCount) (element : XElement) :
    wordField ((foldStore (ncStep 0) (digitCount * 2) memory draws).ram
        (word (Opening.xCell (5 * digit.val + element.slot.val)))) =
      wordField (memory.ram (word (Opening.xCell (5 * digit.val + element.slot.val)))) +
        wordField (memory.ram (word tmpKappa)) *
          designatedVector (freeOf draws) 0 (xElementIndex digit element) := by
  have digitSmall := digit.isLt
  unfold digitCount at digitSmall
  have freeCase : ∀ slot : Fin 2,
      wordField ((foldStore (ncStep 0) (digitCount * 2) memory draws).ram
          (word (Opening.xCell (5 * digit.val + 2 * slot.val)))) =
        wordField (memory.ram (word (Opening.xCell (5 * digit.val + 2 * slot.val)))) +
          wordField (memory.ram (word tmpKappa)) * freeOf draws (digit, slot) := by
    intro slot
    have slotSmall := slot.isLt
    have acc := ncFold_acc (digitCount * 2) 0 (by omega) memory draws (finProdFinEquiv (digit, slot))
    have element : ncElement ((finProdFinEquiv (digit, slot)).val + 0) =
        5 * digit.val + 2 * slot.val := by
      rw [finProdFinEquiv_free]
      unfold ncElement
      omega
    rw [element] at acc
    rw [acc, wordField_fieldWord]
    rfl
  have collectorCase : ∀ slot, slot = 1 ∨ slot = 3 ∨ slot = 4 →
      (foldStore (ncStep 0) (digitCount * 2) memory draws).ram
          (word (Opening.xCell (5 * digit.val + slot))) =
        memory.ram (word (Opening.xCell (5 * digit.val + slot))) := by
    intro slot kind
    refine ncFold_off _ 0 memory draws _ (fun index bound => ⟨?_, ?_⟩)
    · have element := ncElement_lt (index + 0) bound
      exact word_ne (by addr_arith) (by addr_arith) (by addr_arith)
    · have element := ncElement_lt (index + 0) bound
      exact word_ne (by addr_arith) (by addr_arith) (by unfold Opening.xCell ncElement; omega)
  set final := foldStore (ncStep 0) (digitCount * 2) memory draws with finalDef
  set kappaValue := wordField (memory.ram (word tmpKappa)) with kappaDef
  have collectorGoal : ∀ (slot : Nat) (collector : Fin 3), slot = 1 ∨ slot = 3 ∨ slot = 4 →
      wordField (final.ram (word (Opening.xCell (5 * digit.val + slot)))) =
        wordField (memory.ram (word (Opening.xCell (5 * digit.val + slot)))) +
          kappaValue * designatedVector (freeOf draws) 0
            (xElementIndex digit (collectorElement collector)) := by
    intro slot collector kind
    rw [collectorCase slot kind, designatedVector_collector, Pi.zero_apply, mul_zero, add_zero]
  cases element with
  | rowX_x7 =>
      show wordField (final.ram (word (Opening.xCell (5 * digit.val + 2 * (0 : Fin 2).val)))) =
        wordField (memory.ram (word (Opening.xCell (5 * digit.val + 2 * (0 : Fin 2).val)))) +
          kappaValue * designatedVector (freeOf draws) 0 (xElementIndex digit (freeElement 0))
      rw [designatedVector_free]
      exact freeCase 0
  | rowY_mixed =>
      show wordField (final.ram (word (Opening.xCell (5 * digit.val + 2 * (1 : Fin 2).val)))) =
        wordField (memory.ram (word (Opening.xCell (5 * digit.val + 2 * (1 : Fin 2).val)))) +
          kappaValue * designatedVector (freeOf draws) 0 (xElementIndex digit (freeElement 1))
      rw [designatedVector_free]
      exact freeCase 1
  | rowX_x9 => exact collectorGoal 1 0 (by omega)
  | rowY_cubic => exact collectorGoal 3 1 (by omega)
  | rowZ_x9 => exact collectorGoal 4 2 (by omega)


/-! ### From the lifts to the view -/

omit [FieldCertificate] in
theorem kleisli_some (kernel : Memory → PMF (Option Memory)) (memory : Memory) :
    kleisli kernel (some memory) = kernel memory := rfl

omit [FieldCertificate] in
/-- `designatedLimbs` with its abort case as `Option.elim`, for any samplers (so that no sampler
law is unfolded when it is taken apart). -/
theorem designatedLimbs_elim (samplers : Samplers) (table : Public) (bits : BitInput)
    (pointX : Fin pointElementCountX → BaseField) (pointY : Fin pointElementCountY → BaseField)
    (targets : Fin digitCount → FieldMacToECMac.HomogeneousValue) :
    designatedLimbs samplers table bits pointX pointY targets =
      samplers.free.bind fun free => free.elim (PMF.pure none) fun free =>
        samplers.preimage (solvedVector table bits pointX pointY free targets) := by
  unfold designatedLimbs
  congr 1
  funext free
  cases free <;> rfl

variable [GroupCertificate]

omit [FieldCertificate] [GroupCertificate] in
/-- The views agree once the half cells hold the drawn limbs' halves and the rest is untouched. -/
theorem view_eq (memory0 final : Memory) (limbs : DesignatedLimbs)
    (jstar : final.ram (word tmpJStar) = memory0.ram (word tmpJStar))
    (star : final.ram (word designatedLabel) = memory0.ram (word designatedLabel))
    (labels : labelVector final.ram = labelVector memory0.ram)
    (bitsSame : final.bits = memory0.bits)
    (halves : ∀ half : Fin (2 * limbCount .pointX),
      final.ram (word (halfCell half.val)) = blockWord (limbHalf limbs half)) :
    openView final = blocksView memory0 limbs := by
  unfold openView blocksView
  rw [jstar, star, labels, bitsSame]
  congr 1
  funext half
  exact halves half

/-- **The lifts, the non-collectors, the solve and the preimage**, read through the views: P3's
`designatedLimbs` of the target rows of the drawn tail and randomisers. -/
theorem rest_law (source : Stage1Source) (input : AffineInput) (target : Point)
    (pointX : Fin pointElementCountX → BaseField) (pointY : Fin pointElementCountY → BaseField)
    (memory0 : Memory) (pre : OpeningPre source input target pointX pointY memory0)
    (tail : Vector FieldMacToECMac.AffineOffset 90) (lift : Fin digitCount → NonZeroBase)
    (memory : Memory) (same : SameOff memory0.ram memory.ram) (bitsSame : memory.bits = memory0.bits)
    (lamCells : ∀ digit : Fin digitCount,
      memory.ram (word (openLambda digit)) = fieldWord (lift digit).value)
    (pointCells : ∀ digit : Fin digitCount, (memory.ram (word (openPoint digit)),
      memory.ram (word (openPoint digit + 1)), memory.ram (word (openPoint digit + 2))) =
        pointWords (digitPoints target tail digit)) :
    ((Prog.seq Opening.lifts (Prog.seq Opening.nonCollectors (Prog.seq Opening.solve
        (Prog.seq Opening.preimage (.skip 0))))).memSem memory).map (Option.map openView) =
      (designatedLimbs boundedSamplers source.publicValue (BitInput.ofAffine input) pointX pointY
        (targetRows target tail lift)).map (Option.map (blocksView memory0)) := by
  -- the lifts
  set points : Nat → Point := fun digit =>
    if inside : digit < digitCount then digitPoints target tail ⟨digit, inside⟩ else 0
    with pointsDef
  set lams : Nat → BaseField := fun digit =>
    if inside : digit < digitCount then (lift ⟨digit, inside⟩).value else 0 with lamsDef
  obtain ⟨lifted, runLifts, bitsLifted, sameLifted, rowsLifted, _⟩ :=
    memSem_lifts memory points lams
      (fun digit inside => by
        simp only [lamsDef, dif_pos (show digit < digitCount from inside)]
        exact lamCells ⟨digit, inside⟩)
      (fun digit inside => by
        simp only [pointsDef, dif_pos (show digit < digitCount from inside)]
        exact pointCells ⟨digit, inside⟩) 91 le_rfl
  have runLifts' : Opening.lifts.memSem memory = PMF.pure (some lifted) := runLifts
  rw [memSem_pure_seq runLifts']
  have sameToLifted : SameOff memory0.ram lifted.ram := same.trans sameLifted
  -- the non-collectors
  have freeIs : (boundedSamplers).free = freeLaw := rfl
  have preimageIs : (boundedSamplers).preimage = preimageLaw := rfl
  rw [designatedLimbs_elim, freeIs, memSem_seq, memSem_nonCollectors, PMF.bind_map, PMF.map_bind]
  unfold freeLaw
  rw [PMF.bind_map, PMF.map_bind]
  refine congrArg (PMF.bind _) (funext fun drawn => ?_)
  cases drawn with
  | none =>
      show (PMF.pure none : PMF (Option Memory)).map (Option.map openView) =
        (PMF.pure none : PMF (Option DesignatedLimbs)).map (Option.map (blocksView memory0))
      rw [PMF.pure_map, PMF.pure_map]
      rfl
  | some draws =>
  rw [Function.comp_apply, Function.comp_apply, Option.map_some, Option.map_some, kleisli_some,
    Option.elim_some, preimageIs,
    show (fun site => draws (finProdFinEquiv site)) = freeOf draws from rfl]
  set ncd := foldStore (ncStep 0) (digitCount * 2) lifted draws with ncdDef
  have throughNc : ∀ address, (address < accBase ∨ (accBase + 455 ≤ address ∧
      address < designatedBase)) → ncd.ram (word address) = lifted.ram (word address) := by
    intro address where_
    refine ncFold_off _ 0 lifted draws _ (fun index bound => ?_)
    rcases where_ with low | ⟨above, below⟩
    · exact ncAway_low (index + 0) bound address low
    · exact ncAway_mid (index + 0) bound address above below
  have inputIs : (BitInput.ofAffine input).toAffine = input := BitInput.toAffineOfAffine input
  -- the solve
  obtain ⟨solved, runSolve, bitsSolved, sameSolved, targetsSolved, offSolved⟩ := memSem_solve ncd
    (BitInput.ofAffine input).toAffine (kappa (BitInput.ofAffine input))
    (fun digit => source.rows.get digit)
    (fun digit => Pipeline.digitValues (freeFill (BitInput.ofAffine input) pointX (freeOf draws))
      pointY digit)
    (fun digit => targetRows target tail lift digit)
    (by
      rw [throughNc _ (Or.inl (by addr_arith)), sameToLifted _ (not_openCell _ (by addr_arith)),
        pre.reqXCell, wordField_fieldWord, inputIs])
    (by
      rw [throughNc _ (Or.inl (by addr_arith)), sameToLifted _ (not_openCell _ (by addr_arith)),
        pre.reqYCell, wordField_fieldWord, inputIs])
    (by
      rw [throughNc _ (Or.inr ⟨by addr_arith, by addr_arith⟩),
        sameToLifted _ (not_openCell _ (by addr_arith)), pre.kappaCell, wordField_fieldWord])
    (fun digit slot inside => by
      have digitSmall := digit.isLt
      rw [throughNc _ (Or.inl (by addr_arith)), sameToLifted _ (not_openCell _ (by addr_arith)),
        pre.rowCells digit slot inside, wordField_fieldWord, gammaConst_eq_rowField])
    (fun digit element => by
      have digitSmall := digit.isLt
      have slotSmall : element.slot.val < 5 := element.slot.isLt
      rw [nc_value lifted draws digit element, sameToLifted _ (not_openCell _ (by addr_arith)),
        sameToLifted _ (not_openCell _ (by addr_arith)), pre.kappaCell]
      have cell := pre.accXCells (xElementIndex digit element)
      rw [show Opening.xCell (5 * digit.val + element.slot.val) =
        accBase + (xElementIndex digit element).val from rfl, cell, wordField_fieldWord,
        wordField_fieldWord]
      rfl)
    (fun digit element => by
      have digitSmall := digit.isLt
      have slotSmall : element.slot.val < 3 := element.slot.isLt
      rw [throughNc _ (Or.inr ⟨by addr_arith, by addr_arith⟩),
        sameToLifted _ (not_openCell _ (by addr_arith))]
      have cell := pre.accYCells (yElementIndex digit element)
      rw [show Opening.yCell (3 * digit.val + element.slot.val) =
        accBase + 458 + (yElementIndex digit element).val from rfl, cell, wordField_fieldWord]
      rfl)
    (fun digit position inside => by
      have digitSmall := digit.isLt
      rw [throughNc _ (Or.inr ⟨by addr_arith, by addr_arith⟩), rowsLifted digit.val digit.isLt
        position inside]
      simp only [pointsDef, lamsDef, dif_pos (show digit.val < digitCount from digit.isLt)]
      rfl) 91 le_rfl
  have runSolve' : Opening.solve.memSem ncd = PMF.pure (some solved) := runSolve
  rw [memSem_pure_seq runSolve']
  -- the designated cells hold the solved vector
  set vector := solvedVector source.publicValue (BitInput.ofAffine input) pointX pointY
    (freeOf draws) (targetRows target tail lift) with vectorDef
  have freeCell : ∀ (digit : Fin digitCount) (slot : Fin 2),
      solved.ram (word (designatedCell (5 * digit.val + 2 * slot.val))) =
        fieldWord (freeOf draws (digit, slot)) := by
    intro digit slot
    have digitSmall := digit.isLt
    have slotSmall := slot.isLt
    unfold digitCount at digitSmall
    rw [offSolved _ (fun digit' below collector inside => word_ne (by addr_arith) (by addr_arith)
      (by
        unfold collectorCell designatedCell
        rcases (show collector = 0 ∨ collector = 1 ∨ collector = 2 by omega) with h | h | h <;>
          subst h <;> simp only [collectorSlot] <;> omega))]
    have cell := ncFold_designated (digitCount * 2) 0 (by omega) lifted draws
      (finProdFinEquiv (digit, slot))
    have element : ncElement ((finProdFinEquiv (digit, slot)).val + 0) =
        5 * digit.val + 2 * slot.val := by
      rw [finProdFinEquiv_free]
      unfold ncElement
      omega
    rw [element] at cell
    exact cell
  have collectorCellIs : ∀ (digit : Fin digitCount) (collector : Fin 3),
      solved.ram (word (collectorCell digit.val collector.val)) =
        fieldWord (collectorTargets (BitInput.ofAffine input)
          (freeRows source.publicValue (BitInput.ofAffine input) pointX pointY (freeOf draws))
          (targetRows target tail lift) (digit, collector)) := by
    intro digit collector
    rw [targetsSolved digit digit.isLt collector.val collector.isLt, solveWords_component]
    have getIs : (freeRows source.publicValue (BitInput.ofAffine input) pointX pointY
        (freeOf draws)).get digit =
        FieldMacToECMac.evaluateGamma (source.rows.get digit) (BitInput.ofAffine input).toAffine
          (Pipeline.digitValues (freeFill (BitInput.ofAffine input) pointX (freeOf draws))
            pointY digit) := Vector.get_ofFn _ _
    unfold collectorTargets
    rw [getIs]
  have designatedCells : ∀ element : Fin pointElementCountX,
      solved.ram (word (designatedCell element.val)) = fieldWord (vector element) := by
    have key : ∀ (digit : Fin digitCount) (kind : XElement),
        solved.ram (word (designatedCell (xElementIndex digit kind).val)) =
          fieldWord (vector (xElementIndex digit kind)) := by
      intro digit kind
      rw [vectorDef]
      unfold solvedVector
      cases kind with
      | rowX_x7 =>
          rw [show xElementIndex digit .rowX_x7 = xElementIndex digit (freeElement 0) from rfl,
            designatedVector_free]
          exact freeCell digit 0
      | rowY_mixed =>
          rw [show xElementIndex digit .rowY_mixed = xElementIndex digit (freeElement 1) from rfl,
            designatedVector_free]
          exact freeCell digit 1
      | rowX_x9 =>
          rw [show xElementIndex digit .rowX_x9 = xElementIndex digit (collectorElement 0) from rfl,
            designatedVector_collector]
          exact collectorCellIs digit 0
      | rowY_cubic =>
          rw [show xElementIndex digit .rowY_cubic = xElementIndex digit (collectorElement 1) from rfl,
            designatedVector_collector]
          exact collectorCellIs digit 1
      | rowZ_x9 =>
          rw [show xElementIndex digit .rowZ_x9 = xElementIndex digit (collectorElement 2) from rfl,
            designatedVector_collector]
          exact collectorCellIs digit 2
    intro element
    have := key (elementDigit element) (elementKind element)
    rwa [xElementIndex_elementDigit_elementKind] at this
  -- the preimage
  rw [memSem_seq, memSem_preimage solved vector designatedCells, PMF.bind_map]
  have skipIs : (kleisli (Prog.skip 0).memSem ∘ Option.map (BigInt.samplerFinal samplerBase
      BigInt.samplerLimbs BigInt.samplerDigits (vectorEnc vector) solved)) =
      PMF.pure ∘ Option.map (BigInt.samplerFinal samplerBase BigInt.samplerLimbs
        BigInt.samplerDigits (vectorEnc vector) solved) := by
    funext result
    cases result <;> rfl
  unfold preimageLaw
  rw [skipIs, PMF.bind_pure_comp, PMF.map_comp, PMF.map_comp]
  refine congrArg (PMF.map · _) (funext fun kept => ?_)
  cases kept with
  | none => rfl
  | some t =>
      simp only [Function.comp_apply, Option.map_some]
      refine congrArg some (view_eq memory0 _ _ ?_ ?_ ?_ ?_ fun half => ?_)
      · rw [samplerFinal_sameOff _ _ _ _ (not_openCell _ (by addr_arith)),
          sameSolved _ (not_openCell _ (by addr_arith)),
          throughNc _ (Or.inr ⟨by addr_arith, by addr_arith⟩),
          sameToLifted _ (not_openCell _ (by addr_arith))]
      · rw [samplerFinal_sameOff _ _ _ _ (not_openCell _ (by addr_arith)),
          sameSolved _ (not_openCell _ (by addr_arith)),
          throughNc _ (Or.inr ⟨by addr_arith, by addr_arith⟩),
          sameToLifted _ (not_openCell _ (by addr_arith))]
      · rw [labelVector_sameOff (samplerFinal_sameOff _ _ _), labelVector_sameOff sameSolved,
          labelVector_nc _ le_rfl, labelVector_sameOff sameToLifted]
      · rw [samplerFinal_bits, bitsSolved, ncFold_bits, bitsLifted, bitsSame]
      · rw [samplerFinal_half _ _ _ half.val half.isLt, halfValue_limbHalf]

/-! ### The head, the randomisers, and the whole opening -/

/-- The head clamp's point. -/
abbrev headPoint (target : Point) (points : Fin 90 → FieldMacToECMac.AffineOffset) : Point :=
  target - radix • pointHorner radix (FieldMacToECMac.freeOffsetPoints (Vector.ofFn points))

/-- The memory after the tail and the head clamp. -/
abbrev headMem (memory : Memory) (target : Point) (points : Fin 90 → FieldMacToECMac.AffineOffset) :
    Memory :=
  clearRegs (withRam (tailFold memory points) (putPoint (tailFold memory points).ram (openPoint 0)
    (pointWords (headPoint target points)))) headScratch

omit [FieldCertificate] [GroupCertificate] in
theorem wordAt_eq_triple (words : Word × Word × Word) (first second third : Word)
    (h0 : first = wordAt words 0) (h1 : second = wordAt words 1) (h2 : third = wordAt words 2) :
    (first, second, third) = words := by
  rw [h0, h1, h2]; rfl

/-- The digit points sit at `openPoint d` after the tail, the head and the randomisers. -/
theorem pointCells_after (memory : Memory) (target : Point)
    (points : Fin 90 → FieldMacToECMac.AffineOffset) (lams : Fin digitCount → NonZeroBase)
    (digit : Fin digitCount) :
    ((foldStore lamMem 91 (headMem memory target points) lams).ram (word (openPoint digit)),
      (foldStore lamMem 91 (headMem memory target points) lams).ram (word (openPoint digit + 1)),
      (foldStore lamMem 91 (headMem memory target points) lams).ram (word (openPoint digit + 2))) =
        pointWords (digitPoints target (Vector.ofFn points) digit) := by
  have digitSmall : digit.val < 91 := digit.isLt
  have lamOff : ∀ position, position < 3 →
      (foldStore lamMem 91 (headMem memory target points) lams).ram (word (openPoint digit + position)) =
        putPoint (tailFold memory points).ram (openPoint 0) (pointWords (headPoint target points))
          (word (openPoint digit + position)) := by
    intro position inside
    refine (lamFold_off (headMem memory target points) lams (word (openPoint digit + position))
      (fun index bound => word_ne (by unfold openPoint openBase; omega)
        (by unfold openLambda openBase; omega) (by unfold openPoint openLambda; omega))).trans ?_
    unfold headMem
    rw [(clearRegs_other _ _).1, withRam_ram]
  have atCell : ∀ position, position < 3 →
      putPoint (tailFold memory points).ram (openPoint 0) (pointWords (headPoint target points))
          (word (openPoint digit + position)) =
        wordAt (pointWords (digitPoints target (Vector.ofFn points) digit)) position := by
    intro position inside
    by_cases head : digit.val = 0
    · rw [head, putPoint_at _ _ _ _ (by unfold openPoint openBase; omega) inside]
      unfold digitPoints
      rw [dif_pos head]
    · rw [putPoint_off _ _ _ _ (fun position' inside' => word_ne
          (by unfold openPoint openBase; omega) (by unfold openPoint openBase; omega)
          (by unfold openPoint; omega))]
      have tailCell := tailFold_at memory points ⟨digit.val - 1, by omega⟩ position inside
      have digitIs : (⟨digit.val - 1, by omega⟩ : Fin 90).val + 1 = digit.val := by
        show digit.val - 1 + 1 = digit.val; omega
      rw [digitIs, offsetWords_eq] at tailCell
      rw [tailCell]
      unfold digitPoints
      rw [dif_neg head]
      have getIs : (Vector.ofFn points).get ⟨digit.val - 1, by omega⟩ =
          points ⟨digit.val - 1, by omega⟩ := Vector.get_ofFn _ _
      rw [getIs]
  apply wordAt_eq_triple
  · have := lamOff 0 (by omega)
    rw [Nat.add_zero] at this
    rw [this, ← Nat.add_zero (openPoint digit), atCell 0 (by omega)]
  · rw [lamOff 1 (by omega), atCell 1 (by omega)]
  · rw [lamOff 2 (by omega), atCell 2 (by omega)]

theorem headMem_ram (memory : Memory) (target : Point)
    (points : Fin 90 → FieldMacToECMac.AffineOffset) :
    (headMem memory target points).ram = putPoint (tailFold memory points).ram (openPoint 0)
      (pointWords (headPoint target points)) := by
  unfold headMem
  rw [(clearRegs_other _ _).1, withRam_ram]

theorem headMem_bits (memory : Memory) (target : Point)
    (points : Fin 90 → FieldMacToECMac.AffineOffset) :
    (headMem memory target points).bits = memory.bits := by
  unfold headMem
  rw [(clearRegs_other _ _).2, withRam_bits, tailFold_bits]

omit [GroupCertificate] in
/-- `memSem_lambdas` with the randomisers indexed by `Fin digitCount` (as `liftLaw` draws them). -/
theorem memSem_lambdas_digit (memory : Memory) :
    Opening.lambdas.memSem memory =
      liftLaw.map (Option.map fun lams : Fin digitCount → NonZeroBase => foldStore lamMem 91 memory lams) :=
  memSem_lambdas memory

/-- **The randomisers onward**: the machine after the head clamp against P3's lift step. -/
theorem lift_law (source : Stage1Source) (input : AffineInput) (target : Point)
    (pointX : Fin pointElementCountX → BaseField) (pointY : Fin pointElementCountY → BaseField)
    (memory : Memory) (pre : OpeningPre source input target pointX pointY memory)
    (points : Fin 90 → FieldMacToECMac.AffineOffset) :
    ((Prog.seq Opening.lambdas (Prog.seq Opening.lifts (Prog.seq Opening.nonCollectors
        (Prog.seq Opening.solve (Prog.seq Opening.preimage (.skip 0)))))).memSem
          (headMem memory target points)).map (Option.map openView) =
      (liftLaw.bind fun lift => match lift with
        | none => PMF.pure none
        | some lift => designatedLimbs boundedSamplers source.publicValue (BitInput.ofAffine input)
            pointX pointY (targetRows target (Vector.ofFn points) lift)).map
        (Option.map (blocksView memory)) := by
  rw [memSem_seq, memSem_lambdas_digit, PMF.bind_map, PMF.map_bind, PMF.map_bind]
  refine congrArg (PMF.bind _) (funext fun drawn => ?_)
  cases drawn with
  | none => simp [kleisli, PMF.pure_map]
  | some lams =>
      simp only [Function.comp_apply, Option.map_some, kleisli]
      have sameHead : SameOff (tailFold memory points).ram (headMem memory target points).ram := by
        rw [headMem_ram]
        exact sameOff_putPoint _ 0 (by norm_num) _
      exact rest_law source input target pointX pointY memory pre (Vector.ofFn points) lams
        (foldStore lamMem 91 (headMem memory target points) lams)
        (((tailFold_sameOff memory points).trans sameHead).trans
          (lamFold_sameOff (headMem memory target points) lams))
        ((lamFold_bits (headMem memory target points) lams).trans (headMem_bits memory target points))
        (fun digit => lamFold_at (headMem memory target points) lams digit)
        (fun digit => pointCells_after memory target points lams digit)

omit [FieldCertificate] [GroupCertificate] in
/-- **The opening law** (`OpeningLaw`, `Stage2Spec.lean`): the machine's oracle-free opening,
read through `openView`, is `openingLimbs boundedSamplers …` read through `blocksView`. -/
theorem openingLaw : OpeningLaw := by
  intro _ _ source input target pointX pointY memory pre
  have tailIs : (boundedSamplers).tail = tailLaw := rfl
  have liftIs : (boundedSamplers).lift = liftLaw := rfl
  unfold openingFree openingLimbs
  simp only [Prog.seqList]
  rw [memSem_seq, memSem_tail, PMF.bind_map, PMF.map_bind, tailIs, liftIs]
  unfold tailLaw
  rw [PMF.bind_map, PMF.map_bind]
  refine congrArg (PMF.bind _) (funext fun drawn => ?_)
  cases drawn with
  | none => simp [kleisli, PMF.pure_map]
  | some points =>
      simp only [Function.comp_apply, Option.map_some, kleisli, Option.bind_some]
      have request : readWords ((tailFold memory points).ram (word reqTag0),
          (tailFold memory points).ram (word reqQX), (tailFold memory points).ram (word reqQY)) =
            some target := by
        rw [tailFold_sameOff memory points _ (not_openCell _ (by addr_arith)),
          tailFold_sameOff memory points _ (not_openCell _ (by addr_arith)),
          tailFold_sameOff memory points _ (not_openCell _ (by addr_arith)),
          pre.outputCells, readWords_outputWords]
      rw [memSem_seq, memSem_horner _ points target (tailFold_at memory points) request]
      by_cases clamp : FieldMacToECMac.clampedFirst (Vector.ofFn points) = 0
      · rw [if_pos clamp, if_pos clamp, PMF.pure_bind]
        simp [kleisli, PMF.pure_map]
      · rw [if_neg clamp, if_neg clamp, PMF.pure_bind]
        simp only [kleisli]
        exact lift_law source input target pointX pointY memory pre points

end

end Kriterion.ArgoMAC.PlanB.SimMachine
