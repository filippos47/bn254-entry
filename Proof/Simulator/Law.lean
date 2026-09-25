/-
**The machine's laws, in the shape of P3's abstract simulator.**

`MachineLaw planBSimulator (2^-128)` (P3, `Glue/AbstractSimulator.lean`) splits into three
statements, and `machineLaw_of` proves the split:

1. `Stage1Law`: the machine's stage-1 kernel (run, then parse) is
   `planBAbstractSimulator boundedSamplers`'s stage 1, with the retained configuration read back
   as a `Stage1Source` by `extractSource` (exact `PMF` equality);
2. `Stage2Law`: from every stage-1 configuration in the support, the machine's stage-2 kernel
   equals the abstract stage 2 on the extracted source (exact `PMF` equality);
3. `SamplerCutoff`: the abstract game with the machine's bounded samplers is within `2^-128` of
   the one with `idealSamplers` -- a statement about samplers alone, no machine.

`boundedSamplers` are the machine's exact sampler laws, in P3's `Samplers` shape, component by
component: `fieldCellLaw` (bounded rejection over `254` coins below `p`, `rejectLaw`, whose
machine realisation starts from `memSem_sampleWord`), `curvePointLaw` (a uniform finite point by
`x`-rejection and a fair sign), `liftLaw` (`91` randomiser pairs `(λ_d, t_d)`, each two
randomisers in the machine's draw order), `freeLaw` (the designated vector's `91` free
coordinates, `91` field cells in the machine's draw order) and `preimageLaw` (the `t` sampler of
`BigInt.preimageSampler`: `V = enc(Y*) + p^364 · t`, read as its `362` limbs).

What is proved here: the definitions, and `machineLaw_of`. `Stage1Law` (`Stage1Law.lean`),
`Stage2Law` (`Stage2Valid.lean`, `OpeningMachine.lean`) and `SamplerCutoff` (`CutoffMass.lean`)
are proved downstream.
-/

import Proof.Simulator.BigIntAccept
import Proof.Privacy.Phase3.Glue.AbstractSimulator

namespace Kriterion.ArgoMAC.PlanB.SimMachine

open BN254 Cryptography GarbledCircuit Cryptography.BoundedMachine
open Kriterion.ArgoMAC.Phase3.Glue

noncomputable section

/-! ### The machine's sampler laws -/

/-- A RAM word read as a field element. -/
def wordField (value : Word) : BaseField := (value.toNat : BaseField)

/-- One field cell: bounded rejection below `p` (`Stage1.fieldCell`). -/
def fieldCellLaw : PMF (Option BaseField) :=
  (rejectLaw fieldWidth (fun value => decide (value < pNat)) attempts).map
    (Option.map fun (value : Nat) => ((value : Nat) : BaseField))

/-- A uniform `width`-bit word (`Stage1.wordCell`). -/
def wordLaw (width : Nat) : PMF Nat := (PMF.uniformOfFintype (Fin (2 ^ width))).map Fin.val

/-- The stage-1 draws, in the machine's order: field cells, exception bytes, fold joins, key. -/
def stage1Draws : PMF (Option ((Fin fieldCellCount → BaseField) × (Fin exceptionByteCount → Nat) ×
    (Fin hotBlockCount → Nat) × (Fin keyBlockCount → Nat))) :=
  (optionProduct fieldCellCount fun _ => fieldCellLaw).bind fun cells => match cells with
    | none => PMF.pure none
    | some cells =>
      (optionProduct exceptionByteCount fun _ => (wordLaw 8).map some).bind fun bytes =>
      (optionProduct hotBlockCount fun _ => (wordLaw 128).map some).bind fun hot =>
      (optionProduct keyBlockCount fun _ => (wordLaw 128).map some).map fun key =>
        match bytes, hot, key with
        | some bytes, some hot, some key => some (cells, bytes, hot, key)
        | _, _, _ => none

/-- The source a draw publishes and retains. -/
def sourceOfDraws (cells : Nat → BaseField) (bytes hot key : Nat → Nat) : Stage1Source where
  curve := (cells 0, cells 1, cells 2)
  rows := Vector.ofFn fun digit => ⟨cells (3 + 10 * digit), cells (3 + 10 * digit + 1),
    cells (3 + 10 * digit + 2), cells (3 + 10 * digit + 3), cells (3 + 10 * digit + 4),
    cells (3 + 10 * digit + 5), cells (3 + 10 * digit + 6), cells (3 + 10 * digit + 7),
    cells (3 + 10 * digit + 8), cells (3 + 10 * digit + 9)⟩
  exception := Vector.ofFn fun digit => Vector.ofFn fun slot =>
    BitVec.ofNat 8 (bytes (12 * digit + slot))
  curveXHot := Vector.ofFn fun chunk => BitVec.ofNat 128 (hot chunk)
  curveYHot := Vector.ofFn fun chunk => BitVec.ofNat 128 (hot (202 + chunk))
  pointXHot := Vector.ofFn fun chunk => BitVec.ofNat 128 (hot (404 + chunk))
  pointYHot := Vector.ofFn fun chunk => BitVec.ofNat 128 (hot (606 + chunk))
  joins := fun chunk slot => cells (913 + 642 * chunk + slot)
  key := ⟨Vector.ofFn fun bit => ⟨BitVec.ofNat 128 (key (2 * bit)),
      BitVec.ofNat 128 (key (2 * bit + 1))⟩,
    Vector.ofFn fun bit => ⟨BitVec.ofNat 128 (key (2 * (254 + bit))),
      BitVec.ofNat 128 (key (2 * (254 + bit) + 1))⟩⟩

/-- A finite family read as a total function (zero outside). -/
def total {count : Nat} {α : Type} (zero : α) (family : Fin count → α) (index : Nat) : α :=
  if inside : index < count then family ⟨index, inside⟩ else zero

/-- **The machine's stage-1 source law.** -/
def sourceLaw : PMF (Option Stage1Source) :=
  stage1Draws.map (Option.map fun draws =>
    sourceOfDraws (total 0 draws.1) (total 0 draws.2.1) (total 0 draws.2.2.1) (total 0 draws.2.2.2))

/-- The machine's `x`-acceptance: `x < p` and `x³ + 3` a square, witnessed by its
`(p + 1) / 4`-th power. -/
def curveXAccept (value : Nat) : Bool :=
  decide (value < pNat) &&
    decide (((value : BaseField) ^ 3 + 3) ^ sqrtExponent * ((value : BaseField) ^ 3 + 3) ^ sqrtExponent =
      (value : BaseField) ^ 3 + 3)

/-- The point of an accepted `x` and a sign. -/
def curvePointOf (value : Nat) (sign : Bool) : Option FieldMacToECMac.AffineOffset :=
  let root := ((value : BaseField) ^ 3 + 3) ^ sqrtExponent
  let y := if sign then -root else root
  if onCurve : y ^ 2 = (value : BaseField) ^ 3 + 3 then
    some ⟨⟨value, y⟩, onCurve⟩
  else none

/-- One tail point: `x` by bounded rejection, then a fair sign (`Opening.tailOne`). -/
def curvePointLaw : PMF (Option FieldMacToECMac.AffineOffset) :=
  (rejectLaw fieldWidth curveXAccept attempts).bind fun drawn => match drawn with
    | none => PMF.pure none
    | some value => (PMF.uniformOfFintype Bool).map (curvePointOf value)

/-- **The machine's tail law**: `90` points, then the clamp check (`Opening.head` aborts when
`β · H = O`). -/
def tailLaw [FieldCertificate] [GroupCertificate] :
    PMF (Option (Vector FieldMacToECMac.AffineOffset 90)) :=
  (optionProduct 90 fun _ => curvePointLaw).map fun points => points.bind fun points =>
    if FieldMacToECMac.clampedFirst (Vector.ofFn points) = 0 then none
    else some (Vector.ofFn points)

/-- One lift randomiser in `[1, p)` (`Opening.nonZeroCell`). -/
def lambdaLaw : PMF (Option NonZeroBase) :=
  (rejectLaw fieldWidth (fun value => decide (1 ≤ value ∧ value < pNat)) attempts).map
    fun drawn => drawn.bind fun value =>
      if nonzero : (value : BaseField) ≠ 0 then some ⟨value, nonzero⟩ else none

/-- One randomiser pair `(λ, t)` (`Opening.lambdaOne`): `λ`, then `t`. -/
def pairLaw : PMF (Option (NonZeroBase × NonZeroBase)) :=
  (optionProduct 2 fun _ => lambdaLaw).map (Option.map fun pair => (pair 0, pair 1))

/-- **The machine's lift law.** -/
def liftLaw : PMF (Option (Fin digitCount → NonZeroBase × NonZeroBase)) :=
  optionProduct digitCount fun _ => pairLaw

/-- **The machine's free-coordinate law** (`Opening.nonCollectors`): `91` field cells, drawn in
the machine's order, draw `d` being the free coordinate `(d, 0)` (element `4d`). -/
def freeLaw : PMF (Option (FreeSite → BaseField)) :=
  (optionProduct (digitCount * 1) fun _ => fieldCellLaw).map
    (Option.map fun draws site => draws (finProdFinEquiv site))

/-- The digits of a designated vector, as the preimage sampler reads them from its cells. -/
def vectorDigits (vector : Fin pointElementCountX → BaseField) (element : Nat) : Nat :=
  if inside : element < pointElementCountX then (vector ⟨element, inside⟩).val else 0

/-- The base-`p` encoding `enc(Y*)` the preimage sampler forms. -/
def vectorEnc (vector : Fin pointElementCountX → BaseField) : Nat :=
  BigInt.encNat (vectorDigits vector) BigInt.samplerDigits

/-- **The machine's preimage law** (`BigInt.preimageSampler`): `t` by bounded rejection over
`363` coins with `80` attempts, accepted iff `enc(Y*) + p^364 · t < 2^92672`, then the `362`
hash answers of `V = t · p^364 + enc(Y*)`. -/
def preimageLaw (vector : Fin pointElementCountX → BaseField) : PMF (Option DesignatedLimbs) :=
  (rejectLaw (BigInt.hiWidth + 256) (BigInt.samplerAccept (vectorEnc vector))
      BigInt.samplerAttempts).map
    (Option.map fun t => natToLimbs (limbCount .pointX)
      (BigInt.samplerValue BigInt.samplerDigits (vectorEnc vector) t))

/-- **The machine's samplers.** -/
def boundedSamplers [FieldCertificate] [GroupCertificate] : Samplers where
  source := sourceLaw
  tail := tailLaw
  lift := liftLaw
  free := freeLaw
  preimage := preimageLaw

/-! ### The retained state -/

/-- The stage-1 source read back from a machine memory. -/
def extractSource (memory : Memory) : Stage1Source :=
  sourceOfDraws (fun index => wordField (memory.ram (word (fieldBase + index))))
    (fun index => (memory.ram (word (exceptionBase + index))).toNat)
    (fun index => (memory.ram (word (hotBase + index))).toNat)
    (fun index => (memory.ram (word (keyBase + index))).toNat)

/-! ### The three statements and the split -/

section Laws

/-- The machine read as an abstract simulator, at the instances `Solution.adaptivePrivacy`
installs. -/
def machineKernels [FieldCertificate] :=
  @machineAbstract _ PlanB.FixedIndex EncPRF.PermutationIndex PlanB.Public
    (Fintype.ofFinite _) (Fintype.ofFinite _) (Classical.decEq _) (Classical.decEq _)
    Wire.encoding 1103204 planBSimulator

/-- The abstract simulator of the machine's samplers, at the same instances. -/
def boundedKernels [FieldCertificate] [GroupCertificate] :=
  @planBAbstractSimulator _ _ (Classical.decEq _) (Classical.decEq _) boundedSamplers

/-- **Stage-1 law**: exact. -/
def Stage1Law : Prop :=
  ∀ [FieldCertificate] [GroupCertificate] (parameter : Nat),
    (boundedKernels).stage1 parameter LazyOracle.empty =
      ((machineKernels).stage1 parameter LazyOracle.empty).map
        (Option.map fun result => (result.1, extractSource result.2.1.memory, result.2.2))

/-- **Stage-2 law**: exact, from every stage-1 configuration in the support. -/
def Stage2Law : Prop :=
  ∀ [FieldCertificate] [GroupCertificate] (parameter : Nat) result,
    some result ∈ ((machineKernels).stage1 parameter LazyOracle.empty).support →
      ∀ input output oracle, (boundedKernels).stage2 (extractSource result.2.1.memory) input output
        oracle = (machineKernels).stage2 result.2.1 input output oracle

/-- **The sampler cutoff**: bounded samplers versus exact ones, in the abstract game. -/
def SamplerCutoff : Prop :=
  ∀ (field : FieldCertificate) (group : @GroupCertificate field) (adversary : PlanBAdversary Unit)
    (parameter : Nat) (scalar : NonZeroScalar),
    Assumptions.advantage (atSolution idealHybrid field group adversary parameter scalar)
      (@planBIdealGame field group (Classical.decEq _) (Classical.decEq _) Unit boundedSamplers
        adversary parameter scalar ()) ≤ machineCutoffError

/-- **The split.** The machine's two exact stage laws and the sampler cutoff give P3's
`MachineLaw` for `planBSimulator` at `machineCutoffError = 2^-128`. -/
theorem machineLaw_of (stage1 : Stage1Law) (stage2 : Stage2Law) (cutoff : SamplerCutoff) :
    MachineLaw planBSimulator machineCutoffError := by
  intro field group adversary parameter scalar
  have exact : atSolution (machineHybrid planBSimulator) field group adversary parameter scalar =
      @planBIdealGame field group (Classical.decEq _) (Classical.decEq _) Unit boundedSamplers
        adversary parameter scalar () := by
    unfold atSolution machineHybrid planBIdealGame
    beta_reduce
    rw [@idealGame_eq_machineAbstract]
    exact (@abstractIdealGame_eq_of_simulation _ _ _ _ _ _ _ _ (Classical.decEq _)
      (Classical.decEq _) Scheme.scheme machineKernels boundedKernels
      (fun configuration => extractSource configuration.memory) (fun parameter => stage1 parameter)
      (fun parameter result member => stage2 parameter result member) adversary parameter scalar
      ()).symm
  rw [exact]
  exact cutoff field group adversary parameter scalar

end Laws

end

end Kriterion.ArgoMAC.PlanB.SimMachine
