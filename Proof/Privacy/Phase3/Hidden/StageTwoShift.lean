/-
**Phase 3, P1h — the stage-2 tape shifts, at every chunk width.**

Three join-keeping `TapeShift` families, each parametrised by `c : Block`:

* **`familyDeltaU κ u c`** (the Δ-family of coordinate `κ` at the input `u`): `Δ_κ += c`, the zero
  label of every bit of `κ` that `u` sets `+= c` (so every label of `u` is kept:
  `zero ⊕ u·(Δ ⊕ c) ⊕ c·u = zero ⊕ u·Δ`), and per chunk, at every paid step whose bit `u` sets, the
  step material of the active parent `+= c`. At every level exactly the active entry moves, by `c`
  (`FoldShift.level_active`): every **inactive** fold gate keeps its point and output
  (`deltaU_hot_off`), every **inactive** switch its label (`deltaU_level_off`); the active parents'
  points and the active switch's label move by `c` (`deltaU_hot_on`, `deltaU_level_on`); a gadget
  position moves by `c` iff `u`'s bit differs from the exceptional input's (`deltaU_gadget`).
* **`familyKey2 t c`** (off the curve): `k₂ += c`, so every point-lane zero label moves by `c`; per
  point-lane chunk, at every paid step, the material of the parent routed towards the target `t`
  (`pathRoute`) absorbs it. The curve lanes are untouched (`key2_level_curve`, `key2_hot_curve`); in every point
  lane the level label of the target moves by `c` at every level (`key2_level_point`), in
  particular the fold gate `(n, t)` and the switch `t`; every gadget position moves by `c`.
* **`familyHotOut ℓ k n r c`**: both outputs of the fold gate `(ℓ, k, n, r)` move by `c`, nothing
  else moves (`hotOut_hot`, `hotOut_level`).
-/

import Proof.Privacy.Phase3.Hidden.Designed

set_option linter.unusedSectionVars false
set_option maxRecDepth 8000

namespace Kriterion.ArgoMAC.Security.Phase3

open BN254 Cryptography GarbledCircuit Kriterion.ArgoMAC.PlanB
open Kriterion.ArgoMAC.Scheme (Coins Oracle)
open Hidden

noncomputable section

/-! ### A quiet fold and the chunk bits -/

/-- A fold shift that moves no `Δ`, no zero label and no material moves no level label. -/
theorem Hidden.FoldShift.level_quiet (F : FoldShift) (width : Nat) (delta : F.delta = 0)
    (zero : ∀ n, n < width → F.zero n = 0) (m : ∀ n r, 1 ≤ n → n < width → F.m n r = 0) :
    ∀ n, n ≤ width → ∀ j, j < 2 ^ n → F.level n j = 0 := by
  intro n small j entry
  have level := F.level_active 0 width 0 delta (fun n h => by rw [zero n h, ite_self])
    (fun n r one h => by rw [m n r one h, ite_self]) n small j entry
  rwa [ite_self] at level

/-- The bit of a chunk at a step is the input's bit at that position. -/
theorem chunk_bit (bits : BitVec PlanB.coordinateBits) (k : Fin chunkCount) (n : Nat)
    (small : n < chunkWidth k) :
    bits.getLsb (chunkBitIndex k ⟨n, small⟩) = decide ((chunkOf bits k).val / 2 ^ n % 2 = 1) := by
  rw [← Nat.testBit_eq_decide_div_mod_eq]
  show bits.toNat.testBit (chunkOffset k + n) =
    (bits.toNat >>> chunkOffset k % 2 ^ chunkWidth k).testBit n
  rw [Nat.testBit_mod_two_pow, Nat.testBit_shiftRight, decide_eq_true small, Bool.true_and]

/-! ### The Δ-family -/

/-- The active switch of a chunk at the input. -/
def activeOf (input : AffineInput) (κ : Coord) (k : Fin chunkCount) : Nat :=
  (chunkOf (inputBits input κ) k).val

/-- **The Δ-family of coordinate `κ` at the input.** -/
def familyDeltaU (κ : Coord) (input : AffineInput) (c : Block) : TapeShift where
  delta κ' := if κ' = κ then c else 0
  zero κ' p := if κ' = κ ∧ (inputBits input κ).getLsb p = true then c else 0
  key2 := 0
  m ℓ k n r := if (ℓ.coord = κ ∧ activeOf input κ k / 2 ^ n % 2 = 1) ∧
    r = activeOf input κ k % 2 ^ n then c else 0
  o _ _ _ _ := 0

/-- The Δ-family's fold shift at a lane of coordinate `κ`: an active-path family. -/
theorem deltaU_fold (κ : Coord) (input : AffineInput) (c : Block) (ℓ : Lane) (k : Fin chunkCount)
    (hκ : ℓ.coord = κ) :
    (((familyDeltaU κ input c).lane ℓ).fold k).delta = c ∧
    (∀ n, n < chunkWidth k → (((familyDeltaU κ input c).lane ℓ).fold k).zero n =
      if activeOf input κ k / 2 ^ n % 2 = 1 then c else 0) ∧
    (∀ n r, (((familyDeltaU κ input c).lane ℓ).fold k).m n r =
      if r = activeOf input κ k % 2 ^ n ∧ activeOf input κ k / 2 ^ n % 2 = 1 then c else 0) := by
  refine ⟨?_, fun n small => ?_, fun n r => ?_⟩
  · show (if ℓ.coord = κ then c else 0) = c
    rw [if_pos hκ]
  · rw [lane_fold_zero _ _ _ _ small]
    show (if ℓ.coord = κ ∧ (inputBits input κ).getLsb (chunkBitIndex k ⟨n, small⟩) = true then c
      else 0) ^^^ (if laneIsPoint ℓ then 0 else 0) = _
    rw [chunk_bit, ite_self, bxor_zero]
    simp only [hκ, true_and, decide_eq_true_eq]
    rfl
  · show (if (ℓ.coord = κ ∧ activeOf input κ k / 2 ^ n % 2 = 1) ∧
      r = activeOf input κ k % 2 ^ n then c else 0) = _
    simp only [hκ, true_and, and_comm]

/-- At a lane of another coordinate, the Δ-family moves nothing. -/
theorem deltaU_fold_other (κ : Coord) (input : AffineInput) (c : Block) (ℓ : Lane)
    (k : Fin chunkCount) (hκ : ℓ.coord ≠ κ) :
    (((familyDeltaU κ input c).lane ℓ).fold k).delta = 0 ∧
    (∀ n, n < chunkWidth k → (((familyDeltaU κ input c).lane ℓ).fold k).zero n = 0) ∧
    (∀ n r, (((familyDeltaU κ input c).lane ℓ).fold k).m n r = 0) := by
  refine ⟨?_, fun n small => ?_, fun n r => ?_⟩
  · show (if ℓ.coord = κ then c else 0) = 0
    rw [if_neg hκ]
  · rw [lane_fold_zero _ _ _ _ small]
    show (if ℓ.coord = κ ∧ _ then c else 0) ^^^ (if laneIsPoint ℓ then 0 else 0) = 0
    rw [if_neg (fun h => hκ h.1), ite_self, bxor_zero]
  · show (if (ℓ.coord = κ ∧ _) ∧ _ then c else 0) = 0
    rw [if_neg (fun h => hκ h.1.1)]

theorem familyDeltaU_valid (κ : Coord) (input : AffineInput) (c : Block) :
    (familyDeltaU κ input c).Valid := by
  intro ℓ k n one small
  by_cases hκ : ℓ.coord = κ
  · obtain ⟨-, zero, m⟩ := deltaU_fold κ input c ℓ k hκ
    rw [zero n small]
    have reorder : (fun r : Fin (2 ^ n) => (((familyDeltaU κ input c).lane ℓ).fold k).m n r.val) =
        fun r => if activeOf input κ k / 2 ^ n % 2 = 1 ∧ r.val = activeOf input κ k % 2 ^ n then c
          else 0 :=
      funext fun r => by simp only [m, and_comm]
    show xorFold (fun r : Fin (2 ^ n) => (((familyDeltaU κ input c).lane ℓ).fold k).m n r.val) = _
    rw [reorder]
    exact xorFold_single_nat (2 ^ n) (activeOf input κ k % 2 ^ n) (Nat.mod_lt _ (Nat.two_pow_pos n))
      (activeOf input κ k / 2 ^ n % 2 = 1) c
  · obtain ⟨-, zero, m⟩ := deltaU_fold_other κ input c ℓ k hκ
    rw [zero n small]
    show xorFold (fun r : Fin (2 ^ n) => (((familyDeltaU κ input c).lane ℓ).fold k).m n r.val) = 0
    simp only [m]
    exact xorFold_zero

/-- **The Δ-family moves exactly the active entry of every level, by `c`**, at a lane of
coordinate `κ`. -/
theorem deltaU_level (κ : Coord) (input : AffineInput) (c : Block) (ℓ : Lane) (k : Fin chunkCount)
    (hκ : ℓ.coord = κ) (n : Nat) (small : n ≤ chunkWidth k) (j : Nat) (entry : j < 2 ^ n) :
    (((familyDeltaU κ input c).lane ℓ).fold k).level n j =
      if j = activeOf input κ k % 2 ^ n then c else 0 := by
  obtain ⟨delta, zero, m⟩ := deltaU_fold κ input c ℓ k hκ
  exact FoldShift.level_active _ _ (chunkWidth k) c delta zero (fun n r _ _ => m n r) n small j
    entry

theorem deltaU_level_other (κ : Coord) (input : AffineInput) (c : Block) (ℓ : Lane)
    (k : Fin chunkCount) (hκ : ℓ.coord ≠ κ) (n : Nat) (small : n ≤ chunkWidth k) (j : Nat)
    (entry : j < 2 ^ n) : (((familyDeltaU κ input c).lane ℓ).fold k).level n j = 0 := by
  obtain ⟨delta, zero, m⟩ := deltaU_fold_other κ input c ℓ k hκ
  exact FoldShift.level_quiet _ (chunkWidth k) delta zero (fun n r _ _ => m n r) n small j entry

/-- **The Δ-family keeps every inactive fold gate.** -/
theorem deltaU_hot_off (κ : Coord) (input : AffineInput) (c : Block) (ℓ : Lane)
    (k : Fin chunkCount) (n r : Nat) (half : Bool) (small : n < chunkWidth k) (entry : r < 2 ^ n)
    (off : r ≠ activeOf input ℓ.coord k % 2 ^ n) :
    (((familyDeltaU κ input c).lane ℓ).fold k).hot n r half = (0, 0) := by
  rw [fold_hot, lane_fold_o]
  by_cases hκ : ℓ.coord = κ
  · subst hκ
    rw [deltaU_level _ input c ℓ k rfl n small.le r entry, if_neg off,
      (deltaU_fold _ input c ℓ k rfl).2.2 n r]
    simp [familyDeltaU, off]
  · rw [deltaU_level_other κ input c ℓ k hκ n small.le r entry,
      (deltaU_fold_other κ input c ℓ k hκ).2.2 n r]
    simp [familyDeltaU]

/-- **The Δ-family moves every active parent's point by `c`.** -/
theorem deltaU_hot_on (κ : Coord) (input : AffineInput) (c : Block) (ℓ : Lane) (k : Fin chunkCount)
    (n : Nat) (half : Bool) (hκ : ℓ.coord = κ) (small : n < chunkWidth k) :
    ((((familyDeltaU κ input c).lane ℓ).fold k).hot n (activeOf input κ k % 2 ^ n) half).1 = c := by
  rw [fold_hot]
  show (((familyDeltaU κ input c).lane ℓ).fold k).level n (activeOf input κ k % 2 ^ n) = c
  rw [deltaU_level κ input c ℓ k hκ n small.le _ (Nat.mod_lt _ (Nat.two_pow_pos n)), if_pos rfl]

/-- **The Δ-family keeps every inactive switch.** -/
theorem deltaU_level_off (κ : Coord) (input : AffineInput) (c : Block) (site : VectorSite)
    (off : site.switch ≠ chunkOf (inputBits input site.lane.coord) site.chunk) :
    siteShift (familyDeltaU κ input c) site = 0 := by
  show (((familyDeltaU κ input c).lane site.lane).fold site.chunk).level (chunkWidth site.chunk)
    site.switch.val = 0
  by_cases hκ : site.lane.coord = κ
  · subst hκ
    rw [deltaU_level _ input c site.lane site.chunk rfl _ le_rfl _ site.switch.isLt,
      if_neg fun h => off (Fin.ext (h.trans (Nat.mod_eq_of_lt (chunkOf _ _).isLt)))]
  · exact deltaU_level_other κ input c site.lane site.chunk hκ _ le_rfl _ site.switch.isLt

/-- **The Δ-family moves the active switch by `c`.** -/
theorem deltaU_level_on (κ : Coord) (input : AffineInput) (c : Block) (site : VectorSite)
    (hκ : site.lane.coord = κ) (on : site.switch = chunkOf (inputBits input κ) site.chunk) :
    siteShift (familyDeltaU κ input c) site = c := by
  show (((familyDeltaU κ input c).lane site.lane).fold site.chunk).level (chunkWidth site.chunk)
    site.switch.val = c
  rw [deltaU_level κ input c site.lane site.chunk hκ _ le_rfl _ site.switch.isLt,
    if_pos (by rw [on]; exact (Nat.mod_eq_of_lt (chunkOf _ _).isLt).symm)]

section Instances

variable [FieldCertificate] [GroupCertificate]

/-- **The Δ-family at a gadget position**: `c` iff the position is `κ`'s and `u`'s bit differs from
the exceptional input's. -/
theorem deltaU_gadget (κ : Coord) (input : AffineInput) (c : Block) (scalar : NonZeroScalar)
    (coins : Coins) (o : Fin digitCount) (κ' : Coord) (position : Fin PlanB.coordinateBits) :
    gadgetShift (familyDeltaU κ input c) scalar coins o κ' position =
      if κ' = κ ∧ (inputBits input κ').getLsb position ≠ exceptionalBit scalar coins.offsets o κ' position
      then c else 0 := by
  unfold gadgetShift
  simp only [familyDeltaU]
  by_cases hκ : κ' = κ
  · subst hκ
    simp only [true_and, if_true]
    cases (inputBits input κ').getLsb position <;>
      cases exceptionalBit scalar coins.offsets o κ' position <;> simp
  · simp [hκ]

theorem scheme_encode (key : InputMacKey) (input : AffineInput) :
    Scheme.scheme.encode key input = Lamport.selectedLabels (key.encode (BitInput.ofAffine input)) := rfl

theorem encode_x_get (key : InputMacKey) (input : BitInput) (i : Nat) (h : i < 254) :
    (key.encode input).x[i] = BitAdaptor.encode key.x[i] (input.xBits.getLsb ⟨i, h⟩) := by
  simp only [InputMacKey.encode, encodeCoordinate, Vector.getElem_ofFn]

theorem encode_y_get (key : InputMacKey) (input : BitInput) (i : Nat) (h : i < 254) :
    (key.encode input).y[i] = BitAdaptor.encode key.y[i] (input.yBits.getLsb ⟨i, h⟩) := by
  simp only [InputMacKey.encode, encodeCoordinate, Vector.getElem_ofFn]

theorem inputMacKey_x_get (coins : Coins) (i : Nat) (h : i < 254) :
    coins.inputMacKey.x[i] = BitAdaptor.Key.mk (coins.inputZero .x ⟨i, h⟩)
      (coins.inputZero .x ⟨i, h⟩ ^^^ coins.inputDelta .x) := by
  simp only [Coins.inputMacKey, Vector.getElem_ofFn]

theorem inputMacKey_y_get (coins : Coins) (i : Nat) (h : i < 254) :
    coins.inputMacKey.y[i] = BitAdaptor.Key.mk (coins.inputZero .y ⟨i, h⟩)
      (coins.inputZero .y ⟨i, h⟩ ^^^ coins.inputDelta .y) := by
  simp only [Coins.inputMacKey, Vector.getElem_ofFn]

/-- A selected label is kept when its shift vanishes. -/
theorem select_shift (b : Bool) (z Δ sz sΔ : Block) (h : (if b then sz ^^^ sΔ else sz) = 0) :
    BitAdaptor.encode (BitAdaptor.Key.mk (z ^^^ sz) (z ^^^ sz ^^^ (Δ ^^^ sΔ))) b =
      BitAdaptor.encode (BitAdaptor.Key.mk z (z ^^^ Δ)) b := by
  cases b
  · simp only [BitAdaptor.encode, Bool.false_eq_true, if_false] at h ⊢
    rw [h, bxor_zero]
  · simp only [BitAdaptor.encode, if_true] at h ⊢
    have : z ^^^ sz ^^^ (Δ ^^^ sΔ) = z ^^^ Δ ^^^ (sz ^^^ sΔ) := by ac_rfl
    rw [this, h, bxor_zero]

/-- **The Δ-family keeps the labels of `u`.** -/
theorem deltaU_encode (κ : Coord) (input : AffineInput) (c : Block) (coins : Coins) :
    Scheme.scheme.encode (shiftCoins (familyDeltaU κ input c) coins).inputMacKey input =
      Scheme.scheme.encode coins.inputMacKey input := by
  rw [scheme_encode, scheme_encode]
  refine congrArg Lamport.selectedLabels ?_
  apply InputMac.ext
  · apply Vector.ext
    intro i h
    rw [encode_x_get, encode_x_get, inputMacKey_x_get, inputMacKey_x_get]
    refine select_shift _ _ _ _ _ ?_
    show (if (coordinateBits input.x).getLsb ⟨i, h⟩ then
        (if Coord.x = κ ∧ (inputBits input κ).getLsb ⟨i, h⟩ = true then c else 0) ^^^
          (if Coord.x = κ then c else 0)
      else if Coord.x = κ ∧ (inputBits input κ).getLsb ⟨i, h⟩ = true then c else 0) = 0
    by_cases hκ : Coord.x = κ
    · subst hκ
      show (if (inputBits input .x).getLsb ⟨i, h⟩ then _ else _) = 0
      cases (inputBits input .x).getLsb ⟨i, h⟩ <;> simp
    · simp [hκ]
  · apply Vector.ext
    intro i h
    rw [encode_y_get, encode_y_get, inputMacKey_y_get, inputMacKey_y_get]
    refine select_shift _ _ _ _ _ ?_
    show (if (coordinateBits input.y).getLsb ⟨i, h⟩ then
        (if Coord.y = κ ∧ (inputBits input κ).getLsb ⟨i, h⟩ = true then c else 0) ^^^
          (if Coord.y = κ then c else 0)
      else if Coord.y = κ ∧ (inputBits input κ).getLsb ⟨i, h⟩ = true then c else 0) = 0
    by_cases hκ : Coord.y = κ
    · subst hκ
      show (if (inputBits input .y).getLsb ⟨i, h⟩ then _ else _) = 0
      cases (inputBits input .y).getLsb ⟨i, h⟩ <;> simp
    · simp [hκ]

end Instances

/-! ### The `k₂`-family -/

/-- **The `k₂`-family towards the target `t`**: `k₂ += c`; per point-lane chunk, at every paid step,
the material of the parent routed towards `t`. -/
def familyKey2 (t : Nat) (c : Block) : TapeShift where
  delta _ := 0
  zero _ _ := 0
  key2 := c
  m ℓ _ n r := if laneIsPoint ℓ = true ∧ r = pathRoute t n % 2 ^ n then c else 0
  o _ _ _ _ := 0

theorem key2_zero (t : Nat) (c : Block) (ℓ : Lane) (k : Fin chunkCount) (n : Nat)
    (small : n < chunkWidth k) :
    (((familyKey2 t c).lane ℓ).fold k).zero n = if laneIsPoint ℓ = true then c else 0 := by
  rw [lane_fold_zero _ _ _ _ small]
  exact bzero_xor _

theorem familyKey2_valid (t : Nat) (c : Block) : (familyKey2 t c).Valid := by
  intro ℓ k n _ small
  rw [key2_zero t c ℓ k n small]
  exact xorFold_single_nat (2 ^ n) (pathRoute t n % 2 ^ n) (Nat.mod_lt _ (Nat.two_pow_pos n))
    (laneIsPoint ℓ = true) c

/-- The `k₂`-family leaves the curve lanes alone. -/
theorem key2_level_curve (t : Nat) (c : Block) (ℓ : Lane) (k : Fin chunkCount)
    (curve : laneIsPoint ℓ = false) (n : Nat) (small : n ≤ chunkWidth k) (j : Nat)
    (entry : j < 2 ^ n) : (((familyKey2 t c).lane ℓ).fold k).level n j = 0 :=
  FoldShift.level_quiet _ (chunkWidth k) rfl
    (fun n small => by rw [key2_zero t c ℓ k n small, curve]; rfl)
    (fun n r _ _ => by
      show (if laneIsPoint ℓ = true ∧ _ then c else 0) = 0
      rw [curve]
      simp) n small j entry

theorem key2_hot_curve (t : Nat) (c : Block) (ℓ : Lane) (k : Fin chunkCount)
    (curve : laneIsPoint ℓ = false) (n r : Nat) (half : Bool) (small : n < chunkWidth k)
    (entry : r < 2 ^ n) : (((familyKey2 t c).lane ℓ).fold k).hot n r half = (0, 0) := by
  rw [fold_hot, key2_level_curve t c ℓ k curve n small.le r entry]
  show ((0 : Block), (0 : Block) ^^^ 0 ^^^
    (if half then 0 else if laneIsPoint ℓ = true ∧ _ then c else 0)) = (0, 0)
  rw [curve]
  simp

/-- **In every point lane the `k₂`-family moves the target's level label by `c` at every level.** -/
theorem key2_level_point (t : Nat) (c : Block) (ℓ : Lane) (k : Fin chunkCount)
    (point : laneIsPoint ℓ = true) :
    ∀ n, 1 ≤ n → n ≤ chunkWidth k → (((familyKey2 t c).lane ℓ).fold k).level n (t % 2 ^ n) = c :=
  FoldShift.level_path _ t (chunkWidth k) c rfl
    (fun n small => by rw [key2_zero t c ℓ k n small, if_pos point])
    (fun n r one _ => by
      show (if laneIsPoint ℓ = true ∧ r = pathRoute t n % 2 ^ n then c else 0) = _
      rw [Nat.mod_eq_of_lt (pathRoute_lt t n one)]
      simp only [point, true_and])

section Instances

variable [FieldCertificate] [GroupCertificate]

theorem key2_gadget (t : Nat) (c : Block) (scalar : NonZeroScalar) (coins : Coins)
    (o : Fin digitCount) (κ : Coord) (position : Fin PlanB.coordinateBits) :
    gadgetShift (familyKey2 t c) scalar coins o κ position = c := by
  unfold gadgetShift
  simp [familyKey2]

theorem shiftCoins_of_zero (T : TapeShift) (delta : ∀ κ, T.delta κ = 0)
    (zero : ∀ κ p, T.zero κ p = 0) (coins : Coins) : shiftCoins T coins = coins := by
  apply Scheme.Coins.data_injective
  have z : (fun κ (position : Fin coordinateBitCount) =>
      coins.inputZero κ position ^^^ T.zero κ position) = coins.inputZero :=
    funext fun κ => funext fun p => by rw [zero κ p, bxor_zero]
  have d : (fun κ => coins.inputDelta κ ^^^ T.delta κ) = coins.inputDelta :=
    funext fun κ => by rw [delta κ, bxor_zero]
  simp only [Scheme.Coins.data, shiftCoins, z, d]

theorem key2_coins (t : Nat) (c : Block) (coins : Coins) :
    shiftCoins (familyKey2 t c) coins = coins :=
  shiftCoins_of_zero _ (fun _ => rfl) (fun _ _ => rfl) coins

end Instances

/-! ### The hot-output family -/

/-- **Both outputs of the fold gate `(ℓ, k, n, r)` move by `c`.** -/
def familyHotOut (ℓ : Lane) (k : Fin chunkCount) (n r : Nat) (c : Block) : TapeShift where
  delta _ := 0
  zero _ _ := 0
  key2 := 0
  m _ _ _ _ := 0
  o ℓ' k' n' r' := if ℓ' = ℓ ∧ k' = k ∧ n' = n ∧ r' = r then c else 0

theorem hotOut_zero (ℓ : Lane) (k : Fin chunkCount) (n r : Nat) (c : Block) (ℓ' : Lane)
    (k' : Fin chunkCount) (n' : Nat) (small : n' < chunkWidth k') :
    (((familyHotOut ℓ k n r c).lane ℓ').fold k').zero n' = 0 := by
  rw [lane_fold_zero _ _ _ _ small]
  show (0 : Block) ^^^ (if laneIsPoint ℓ' then 0 else 0) = 0
  rw [ite_self, bxor_zero]

theorem familyHotOut_valid (ℓ : Lane) (k : Fin chunkCount) (n r : Nat) (c : Block) :
    (familyHotOut ℓ k n r c).Valid := by
  intro ℓ' k' n' _ small
  rw [hotOut_zero ℓ k n r c ℓ' k' n' small]
  exact xorFold_zero

theorem hotOut_level (ℓ : Lane) (k : Fin chunkCount) (n r : Nat) (c : Block) (ℓ' : Lane)
    (k' : Fin chunkCount) (n' : Nat) (small : n' ≤ chunkWidth k') (j : Nat) (entry : j < 2 ^ n') :
    (((familyHotOut ℓ k n r c).lane ℓ').fold k').level n' j = 0 :=
  FoldShift.level_quiet _ (chunkWidth k') rfl (fun n small => hotOut_zero ℓ k n r c ℓ' k' n small)
    (fun _ _ _ _ => rfl) n' small j entry

theorem hotOut_hot (ℓ : Lane) (k : Fin chunkCount) (n r : Nat) (c : Block) (ℓ' : Lane)
    (k' : Fin chunkCount) (n' r' : Nat) (half : Bool) (small : n' < chunkWidth k')
    (entry : r' < 2 ^ n') :
    (((familyHotOut ℓ k n r c).lane ℓ').fold k').hot n' r' half =
      (0, if ℓ' = ℓ ∧ k' = k ∧ n' = n ∧ r' = r then c else 0) := by
  rw [fold_hot, hotOut_level ℓ k n r c ℓ' k' n' small.le r' entry]
  show ((0 : Block), (0 : Block) ^^^ (if ℓ' = ℓ ∧ k' = k ∧ n' = n ∧ r' = r then c else 0) ^^^
    (if half then 0 else 0)) = _
  rw [ite_self, bxor_zero, bzero_xor]

section Instances

variable [FieldCertificate] [GroupCertificate]

theorem hotOut_gadget (ℓ : Lane) (k : Fin chunkCount) (n r : Nat) (c : Block)
    (scalar : NonZeroScalar) (coins : Coins) (o : Fin digitCount) (κ : Coord)
    (position : Fin PlanB.coordinateBits) :
    gadgetShift (familyHotOut ℓ k n r c) scalar coins o κ position = 0 := by
  unfold gadgetShift
  simp [familyHotOut]

theorem hotOut_coins (ℓ : Lane) (k : Fin chunkCount) (n r : Nat) (c : Block) (coins : Coins) :
    shiftCoins (familyHotOut ℓ k n r c) coins = coins :=
  shiftCoins_of_zero _ (fun _ => rfl) (fun _ _ => rfl) coins

end Instances

end

end Kriterion.ArgoMAC.Security.Phase3
