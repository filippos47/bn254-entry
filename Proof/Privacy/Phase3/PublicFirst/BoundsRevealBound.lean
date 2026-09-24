/-
**Phase 3, P1k — (B2) assembled: `RevealBound (planBShadow scalar off) scalar (182/(r − 1))`.**

* `differTargets_card_le` — for a fixed collision set `T`, each digit has at most one offset point
  whose exceptional input differs from `u` exactly on `T` (`exc` is injective off `φ = 0`, the bit
  encoding is injective, a point has one affine form).
* `coins_differ_mul_le` — the coins' offsets hit these targets with mass
  `Pr[∃ o, DiffersOn o T] · (1 − 91/#Point) ≤ 91/#Point` (P1's `tailRho_law`, `values_point`,
  P1e's `goodTails_hit_mul_le`).
* `onCurve_reveal_le` — on the curve, the reveal mass of `M'`'s unflagged private stage 2 is at
  most `Σ_T ε^{|T|} · Pr_coins[∃ o, DiffersOn o T]` (`shadow_reveal_le` after `HW`'s opening, whose
  EncPRF part is exact, `opening_encExact`).
* `reveal_numeric` — `(1 + ε)^508 · 91/#Point ≤ 182/(r − 1) · (1 − 91/#Point)`, from `#Point ≥ r`
  only (Bernoulli: `(1 + ε)^508 ≤ 3/2`).
* **`revealBound_planBShadow`**: `RevealBound (planBShadow scalar off) scalar (ofReal (182/(r−1)))`
  for every off-curve part whose own reveal mass is within the same budget (`OffRevealBound`); the
  off-curve branch of `M'` is exactly the off-curve part's outcome law (`privateStage2U_off`).
-/

import Proof.Privacy.Phase3.PublicFirst.BoundsReveal

set_option linter.unusedSectionVars false
set_option maxRecDepth 8000

namespace Kriterion.ArgoMAC.Security.Phase3.PublicFirst

open BN254 Cryptography GarbledCircuit Kriterion.ArgoMAC.PlanB
open Kriterion.ArgoMAC.Scheme (Coins Oracle)
open Kriterion.ArgoMAC.Security.OperationalOracle
open Kriterion.ArgoMAC.Security.Phase3 (GoodTails)
open Kriterion.ArgoMAC.Phase3.Glue (Stage1Source openingQueriesM interceptAnswer whitePadsM
  idealSamplers programRequests)
open Kriterion.ArgoMAC.Phase3.Lazy (LState Record Cell Tape runRefill uniformMaskTape AllQ)
open scoped ENNReal

noncomputable section

variable [DecidableEq FixedIndex] [DecidableEq EncPRF.PermutationIndex]

/-! ### The coins -/

section Coins

variable [FieldCertificate] [GroupCertificate]

open Classical in
/-- **The offset points of digit `o` whose exceptional input differs from `bits` exactly on `T`.** -/
def differTargets (scalar : NonZeroScalar) (bits : BitInput) (T : Finset EncPRF.PermutationIndex)
    (o : Fin 91) : Finset Point :=
  Finset.univ.filter fun K : Point => ∃ coords : AffineInput, decodePoint coords = some K ∧
    ∃ phi, digitEndomorphismBase ((digitsOf scalar).get o) = some phi ∧
      ∀ j : EncPRF.PermutationIndex,
        (inputBit (BitInput.ofAffine (Exception.exceptionalInput phi coords)) j.1 j.2 ≠
          inputBit bits j.1 j.2 ↔ j ∈ T)

/-- Two bit inputs with the same bits are equal. -/
theorem bitInput_ext {first second : BitInput}
    (same : ∀ j : EncPRF.PermutationIndex, inputBit first j.1 j.2 = inputBit second j.1 j.2) :
    first = second := by
  obtain ⟨x₁, y₁⟩ := first
  obtain ⟨x₂, y₂⟩ := second
  have xs : x₁ = x₂ := BitVec.eq_of_getElem_eq fun i hi => by
    have := same (.x, ⟨i, hi⟩)
    simpa [inputBit] using this
  have ys : y₁ = y₂ := BitVec.eq_of_getElem_eq fun i hi => by
    have := same (.y, ⟨i, hi⟩)
    simpa [inputBit] using this
  rw [xs, ys]

/-- **At most one offset point per digit differs from `bits` exactly on `T`.** -/
theorem differTargets_card_le (scalar : NonZeroScalar) (bits : BitInput)
    (T : Finset EncPRF.PermutationIndex) (o : Fin 91) :
    (differTargets scalar bits T o).card ≤ 1 := by
  classical
  refine Finset.card_le_one.mpr fun K₁ member₁ K₂ member₂ => ?_
  simp only [differTargets, Finset.mem_filter, Finset.mem_univ, true_and] at member₁ member₂
  obtain ⟨coords₁, decode₁, phi₁, digit₁, differ₁⟩ := member₁
  obtain ⟨coords₂, decode₂, phi₂, digit₂, differ₂⟩ := member₂
  rw [digit₁] at digit₂
  cases digit₂
  have sixth := digitEndomorphismBasePowSix _ _ digit₁
  have nonzero : phi₁ ≠ 0 := by
    rintro rfl
    simp at sixth
  have bitsSame : BitInput.ofAffine (Exception.exceptionalInput phi₁ coords₁) =
      BitInput.ofAffine (Exception.exceptionalInput phi₁ coords₂) := by
    refine bitInput_ext fun j => ?_
    have h₁ := differ₁ j
    have h₂ := differ₂ j
    cases a : inputBit (BitInput.ofAffine (Exception.exceptionalInput phi₁ coords₁)) j.1 j.2 <;>
      cases b : inputBit (BitInput.ofAffine (Exception.exceptionalInput phi₁ coords₂)) j.1 j.2 <;>
        cases u : inputBit bits j.1 j.2 <;> simp_all
  have excSame : Exception.exceptionalInput phi₁ coords₁ =
      Exception.exceptionalInput phi₁ coords₂ := by
    rw [← BitInput.toAffineOfAffine (Exception.exceptionalInput phi₁ coords₁), bitsSame,
      BitInput.toAffineOfAffine]
  have coordsSame : coords₁ = coords₂ := by
    obtain ⟨x₁, y₁⟩ := coords₁
    obtain ⟨x₂, y₂⟩ := coords₂
    simp only [Exception.exceptionalInput, AffineInput.mk.injEq] at excSame
    obtain ⟨hx, hy⟩ := excSame
    rw [mul_left_cancel₀ (pow_ne_zero 2 nonzero) hx, mul_left_cancel₀ (pow_ne_zero 3 nonzero) hy]
  subst coordsSame
  rw [decode₁] at decode₂
  exact Option.some.inj decode₂

/-- **A digit differing on `T` puts the coins' clamped offset into its targets.** -/
theorem differsOn_target (scalar : NonZeroScalar) (coins : Coins) (bits : BitInput)
    (T : Finset EncPRF.PermutationIndex) (o : Fin digitCount)
    (differs : DiffersOn scalar coins.offsets bits T o) :
    clampOffsets radixMap (tailPoints coins.offsets) o ∈ differTargets scalar bits T o := by
  classical
  obtain ⟨phi, digit, differ⟩ := differs
  have key := outputKeys_get scalar coins.offsets o
  simp only [outputKeyOf] at digit differ
  rw [key] at digit differ
  simp only [differTargets, Finset.mem_filter, Finset.mem_univ, true_and]
  refine ⟨(coins.offsets.values.get o).coordinates, ?_, phi, digit, differ⟩
  rw [← values_point coins.offsets coins.offsetsClamped o]
  simp only [FieldMacToECMac.AffineOffset.point, Option.some_get]

theorem tsum_mul_ind_eq_outer {X : Type} (μ : PMF X) (S : Set X) :
    ∑' x, μ x * ind (x ∈ S) = μ.toOuterMeasure S := by
  rw [PMF.toOuterMeasure_apply]
  refine tsum_congr fun x => ?_
  by_cases h : x ∈ S
  · rw [ind_pos h, mul_one, Set.indicator_of_mem h]
  · rw [ind_neg h, mul_zero, Set.indicator_of_notMem h]

/-- **The coins differ on `T` with mass `≤ 91/(#Point − 91)`** (in multiplicative form). -/
theorem coins_differ_mul_le (scalar : NonZeroScalar) (bits : BitInput)
    (T : Finset EncPRF.PermutationIndex) :
    letI : Fintype Coins := Fintype.ofFinite Coins
    (∑' coins, PMF.uniformOfFintype Coins coins * ind (∃ o, DiffersOn scalar coins.offsets bits T o))
        * (1 - 91 * (Fintype.card Point : ℝ≥0∞)⁻¹) ≤ 91 * (Fintype.card Point : ℝ≥0∞)⁻¹ := by
  let : Fintype Coins := Fintype.ofFinite Coins
  classical
  set event : GoodTails → Prop := fun tail =>
    ∃ o : Fin 91, clampOffsets radixMap tail.1 o ∈ differTargets scalar bits T o with eventDef
  have step1 : ∑' coins, PMF.uniformOfFintype Coins coins *
        ind (∃ o, DiffersOn scalar coins.offsets bits T o) ≤
      ∑' coins, PMF.uniformOfFintype Coins coins * ind (event (tailRho coins).1) :=
    ENNReal.tsum_le_tsum fun coins => mul_le_mul' le_rfl (ind_mono fun ⟨o, differs⟩ =>
      ⟨o, differsOn_target scalar coins bits T o differs⟩)
  have step2 : ∑' coins, PMF.uniformOfFintype Coins coins * ind (event (tailRho coins).1) =
      ∑' tail, PMF.uniformOfFintype GoodTails tail * ind (event tail) := by
    rw [← tsum_map_mul (PMF.uniformOfFintype Coins) tailRho (fun pair => ind (event pair.1)),
      tailRho_law, ← tsum_map_mul _ Prod.fst (fun tail => ind (event tail)), productPMF_map_fst]
  have step3 : ∑' tail, PMF.uniformOfFintype GoodTails tail * ind (event tail) =
      (PMF.uniformOfFintype GoodTails).toOuterMeasure
        {tail | ∃ digit, clampOffsets radixMap tail.1 digit ∈ differTargets scalar bits T digit} :=
    tsum_mul_ind_eq_outer _ _
  have hit := goodTails_hit_mul_le (differTargets scalar bits T)
  have cards : ((∑ digit : Fin 91, (differTargets scalar bits T digit).card : ℕ) : ℝ≥0∞) ≤ 91 := by
    have : (∑ digit : Fin 91, (differTargets scalar bits T digit).card) ≤ 91 :=
      le_trans (Finset.sum_le_sum fun digit _ => differTargets_card_le scalar bits T digit)
        (by simp)
    exact_mod_cast this
  calc (∑' coins, PMF.uniformOfFintype Coins coins *
          ind (∃ o, DiffersOn scalar coins.offsets bits T o)) *
        (1 - 91 * (Fintype.card Point : ℝ≥0∞)⁻¹)
      ≤ (PMF.uniformOfFintype GoodTails).toOuterMeasure
          {tail | ∃ digit, clampOffsets radixMap tail.1 digit ∈ differTargets scalar bits T digit} *
          (1 - 91 * (Fintype.card Point : ℝ≥0∞)⁻¹) := by
        rw [← step3, ← step2]
        exact mul_le_mul' step1 le_rfl
    _ ≤ _ := le_trans hit (mul_le_mul' cards le_rfl)

end Coins

/-! ### The numbers -/

section Numeric

variable [FieldCertificate] [GroupCertificate]

/-- Bernoulli from above: `(1 + d)^508 ≤ 3/2` when `0 ≤ d` and `508 d ≤ 1/3`. -/
theorem onePlus_pow_le (d : ℝ) (dPos : 0 ≤ d) (dSmall : 508 * d ≤ 1 / 3) :
    (1 + d) ^ 508 ≤ 3 / 2 := by
  have dOne : d ≤ 1 := by linarith
  have base0 : 0 ≤ (1 + d) * (1 - d) := mul_nonneg (by linarith) (by linarith)
  have base1 : (1 + d) * (1 - d) ≤ 1 := by nlinarith
  have prod : (1 + d) ^ 508 * (1 - d) ^ 508 ≤ 1 := by
    rw [← mul_pow]
    exact pow_le_one₀ base0 base1
  have bern : 1 + ((508 : ℕ) : ℝ) * (-d) ≤ (1 + (-d)) ^ 508 :=
    one_add_mul_le_pow (by linarith) 508
  have lower : 2 / 3 ≤ (1 - d) ^ 508 := by
    have same : (1 : ℝ) + ((508 : ℕ) : ℝ) * (-d) = 1 - 508 * d := by push_cast; ring
    rw [same, show (1 : ℝ) + -d = 1 - d by ring] at bern
    clear prod
    generalize (1 - d) ^ 508 = P at bern ⊢
    linarith
  have upper : (1 + d) ^ 508 * (2 / 3) ≤ 1 :=
    le_trans (mul_le_mul_of_nonneg_left lower (by positivity)) prod
  clear prod bern lower
  generalize (1 + d) ^ 508 = Q at upper ⊢
  linarith

/-- `(1 + ε)^508 ≤ 3/2` at `ε = 1/(2^128 − 1)`. -/
theorem onePlusEps_pow_le :
    (1 + 1 / ((2 : ℝ) ^ 128 - 1)) ^ 508 ≤ 3 / 2 :=
  onePlus_pow_le _ (by norm_num) (by norm_num)

/-- The real core of the budget: `E · 91/n ≤ 182/(r − 1) · (1 − 91/n)` for `E ≤ 3/2`,
`1000 ≤ r ≤ n`. -/
theorem numeric_core (E r n : ℝ) (E1 : E ≤ 3 / 2) (rBig : 1000 ≤ r) (hn : r ≤ n) :
    E * (91 * n⁻¹) ≤ 182 / (r - 1) * (1 - 91 * n⁻¹) := by
  have npos : 0 < n := by linarith
  have rpos : 0 < r - 1 := by linarith
  set m : ℝ := n⁻¹ with mDef
  have mpos : 0 < m := inv_pos.mpr npos
  have mn : m * n = 1 := inv_mul_cancel₀ npos.ne'
  have mr : m * r ≤ 1 := by
    calc m * r ≤ m * n := mul_le_mul_of_nonneg_left hn mpos.le
      _ = 1 := mn
  have m1000 : m * 1000 ≤ 1 := le_trans (mul_le_mul_of_nonneg_left rBig mpos.le) mr
  rw [div_mul_eq_mul_div, le_div_iff₀ rpos]
  have step : E * (91 * m) * (r - 1) ≤ 3 / 2 * (91 * m) * (r - 1) :=
    mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right E1 (by positivity)) rpos.le
  nlinarith

/-- **The reveal budget closes from `#Point ≥ r`.** -/
theorem reveal_numeric :
    (epsPad + 1) ^ 508 * (91 * (Fintype.card Point : ℝ≥0∞)⁻¹) ≤
      ENNReal.ofReal Kriterion.ArgoMAC.Phase3.Glue.exceptionalError *
        (1 - 91 * (Fintype.card Point : ℝ≥0∞)⁻¹) := by
  have order := Kriterion.ArgoMAC.Security.Phase3.scalarFieldModulus_le_card_point
  set N : ℕ := Fintype.card Point with NDef
  have rBig : (21888242871839275222246405745257275088548364400416034343698204186575808495617 : ℝ)
      ≤ (N : ℝ) := by
    have : (scalarFieldModulus : ℝ) ≤ (N : ℝ) := by exact_mod_cast order
    simpa [scalarFieldModulus] using this
  have Npos : (0 : ℝ) < N := lt_of_lt_of_le (by norm_num) rBig
  have Nne : (N : ℝ≥0∞) ≠ 0 := by
    have : 0 < N := by exact_mod_cast Npos
    exact_mod_cast this.ne'
  have smallFrac : 91 * (N : ℝ≥0∞)⁻¹ ≤ 1 := by
    rw [← div_eq_mul_inv, ENNReal.div_le_iff Nne (ENNReal.natCast_ne_top _), one_mul]
    have : (91 : ℝ) ≤ N := le_trans (by norm_num) rBig
    exact_mod_cast this
  have epsReal : epsPad.toReal = 1 / ((2 : ℝ) ^ 128 - 1) := by
    rw [ENNReal.toReal_inv, ENNReal.toReal_natCast]
    norm_num
  have lhsTop : (epsPad + 1) ^ 508 * (91 * (N : ℝ≥0∞)⁻¹) ≠ ⊤ :=
    ENNReal.mul_ne_top (ENNReal.pow_ne_top (ENNReal.add_ne_top.mpr
      ⟨ENNReal.inv_ne_top.mpr (by norm_num), ENNReal.one_ne_top⟩))
      (ENNReal.mul_ne_top (by norm_num) (ENNReal.inv_ne_top.mpr Nne))
  have rhsTop : ENNReal.ofReal Kriterion.ArgoMAC.Phase3.Glue.exceptionalError *
      (1 - 91 * (N : ℝ≥0∞)⁻¹) ≠ ⊤ :=
    ENNReal.mul_ne_top ENNReal.ofReal_ne_top (ENNReal.sub_ne_top ENNReal.one_ne_top)
  rw [← ENNReal.toReal_le_toReal lhsTop rhsTop]
  rw [ENNReal.toReal_mul, ENNReal.toReal_pow, ENNReal.toReal_add (ENNReal.inv_ne_top.mpr
      (by norm_num)) ENNReal.one_ne_top, epsReal, ENNReal.toReal_one, ENNReal.toReal_mul,
    ENNReal.toReal_inv, ENNReal.toReal_natCast, ENNReal.toReal_mul,
    ENNReal.toReal_ofReal Kriterion.ArgoMAC.Phase3.Glue.exceptionalError_nonneg,
    ENNReal.toReal_sub_of_le smallFrac ENNReal.one_ne_top, ENNReal.toReal_one, ENNReal.toReal_mul,
    ENNReal.toReal_inv, ENNReal.toReal_natCast]
  have ninetyOne : (ENNReal.toReal 91) = 91 := by norm_num
  rw [ninetyOne]
  unfold Kriterion.ArgoMAC.Phase3.Glue.exceptionalError
  have rBig' : (1000 : ℝ) ≤ (scalarFieldModulus : ℝ) := by norm_num [scalarFieldModulus]
  have hN : (scalarFieldModulus : ℝ) ≤ (N : ℝ) := by exact_mod_cast order
  exact numeric_core _ _ _ (by rw [add_comm]; exact onePlusEps_pow_le) rBig' hN

end Numeric

/-! ### The off-curve part, and the reveal bound -/

section Assembly

variable [FieldCertificate] [GroupCertificate]

open Classical in
/-- **The off-curve part's own law of outcomes** (points, reveal bit). -/
def offOutcome (off : OffShadow) (source : Stage1Source) (input : AffineInput) :
    PMF PrivateOutcome :=
  off.law.bind fun coin =>
    (uniformMaskTape.bind fun tape => runFillFlag LazyOracle.empty (fun cell => PMF.pure (tape cell))
      (off.offCurve source input coin) LazyOracle.empty ∅).map fun shadowed =>
      match shadowed with
      | none => none
      | some result => some (pointsOf result.2, decide (off.revealOff source input coin result.2))

/-- **The off-curve part's reveal hypothesis**: its own reveal mass is `≤ ρ`. -/
def OffRevealBound (off : OffShadow) (ρ : ℝ≥0∞) : Prop :=
  ∀ (source : Stage1Source) (input : AffineInput),
    ∑' o, offOutcome off source input o * revealWeight o ≤ ρ

/-- **Off the curve, `M'`'s unflagged private stage 2 is the off-curve part's outcome law** (the
offsets `Δ` are not read). -/
theorem privateStage2U_off (scalar : NonZeroScalar) (off : OffShadow) (source : Stage1Source)
    (input : AffineInput) :
    privateStage2U uniformMaskTape (planBShadow scalar off) scalar source input none =
      offOutcome off source input := by
  simp only [privateStage2U]
  show ((deltaLaw.bind fun delta => off.law.map fun coin => (delta, coin)).bind _) = _
  refine (PMF.bind_bind _ _ _).trans ?_
  refine Eq.trans ?_ (PMF.bind_const deltaLaw (offOutcome off source input))
  congr 1
  funext delta
  refine (PMF.bind_map _ _ _).trans ?_
  rfl

/-- The on-curve questions of `planBShadow`. -/
theorem planBShadow_onCurve (scalar : NonZeroScalar) (off : OffShadow) (source : Stage1Source)
    (input : AffineInput) (coins : Coins) (delta : EncPRF.Coordinate → Block) (offCoin : off.Coin)
    (ran : ((Fin pointElementCountX → BaseField) × (Fin pointElementCountY → BaseField)) × Record) :
    (planBShadow scalar off).onCurve source input coins (delta, offCoin) ran =
      shadowOnM source.publicValue (restoredBits source input) (restoredMac source input) := by
  unfold planBShadow
  dsimp only

/-- The on-curve reveal flag of `planBShadow`. -/
theorem planBShadow_revealOn (scalar : NonZeroScalar) (off : OffShadow) (source : Stage1Source)
    (input : AffineInput) (coins : Coins) (delta : EncPRF.Coordinate → Block) (offCoin : off.Coin)
    (state : LState) :
    (planBShadow scalar off).revealOn source input coins (delta, offCoin) state =
      revealOnPred scalar source input coins delta state := by
  unfold planBShadow
  dsimp only

theorem revealWeight_some (x : Points FixedIndex EncPRF.PermutationIndex) (p : Prop)
    [Decidable p] : revealWeight (some (x, decide p)) = ind p := by
  by_cases hp : p
  · rw [ind_pos hp]
    simp [revealWeight, hp]
  · rw [ind_neg hp]
    simp [revealWeight, hp]

open Classical in
/-- **On the curve, the reveal mass is at most the collision-set sum over the coins.** -/
theorem onCurve_reveal_le (scalar : NonZeroScalar) (off : OffShadow) (source : Stage1Source)
    (input : AffineInput) (target : Point) :
    letI : Fintype Coins := Fintype.ofFinite Coins
    ∑' o, privateStage2U uniformMaskTape (planBShadow scalar off) scalar source input (some target) o *
        revealWeight o ≤
      ∑' coins, PMF.uniformOfFintype Coins coins *
        ∑ T ∈ (Finset.univ : Finset EncPRF.PermutationIndex).powerset,
          epsPad ^ T.card * ind (∃ o, DiffersOn scalar coins.offsets (restoredBits source input) T o) := by
  let : Fintype Coins := Fintype.ofFinite Coins
  simp only [privateStage2U]
  rw [tsum_bind_mul]
  refine tsum_le_of_support _ _ _ fun tape _ => ?_
  rw [tsum_bind_mul]
  refine tsum_le_of_support _ _ _ fun ran ranMember => ?_
  rcases ran with _ | ran
  · simp only [abortCont, tsum_pure_mul, revealWeight]
    exact zero_le
  · simp only [abortCont]
    -- the opening's final state: prefix stored, EncPRF part exact
    have prefixStored := opening_stores_prefix _ _ _ _ _ _ _ ran ranMember
    have encExact := opening_encExact _ _ _ _ ran ranMember
    unfold privateContU
    dsimp only
    rw [tsum_bind_mul]
    refine ENNReal.tsum_le_tsum fun coins => mul_le_mul' le_rfl ?_
    rw [tsum_bind_mul]
    refine tsum_le_of_support _ _ _ fun answers _ => ?_
    rcases answers with _ | answers
    · simp only [tsum_pure_mul, revealWeight]
      exact zero_le
    · dsimp only
      rw [tsum_bind_mul]
      refine tsum_le_of_support _ _ _ fun coin _ => ?_
      obtain ⟨delta, offCoin⟩ := coin
      rw [tsum_map_mul]
      simp only [revealWeight_some, planBShadow_onCurve, planBShadow_revealOn]
      -- the designated installation touches only the hash part
      have grow := programAllSkip_grows (programRequests (restoredBits source input) ran.2.2 answers)
        ran.2.1
      have stored := (storedPath_grows _ grow prefixStored).1
      have keysSame := (storedPath_grows _ grow prefixStored).2
      have exact : EncExact (programAllSkip (programRequests (restoredBits source input) ran.2.2
          answers) ran.2.1) (prefixKeysOn (programAllSkip (programRequests (restoredBits source input)
            ran.2.2 answers) ran.2.1) source.publicValue (restoredBits source input)
              (restoredMac source input)).1 := by
        have sameKeys : prefixKeysOn (programAllSkip (programRequests (restoredBits source input)
            ran.2.2 answers) ran.2.1) source.publicValue (restoredBits source input)
              (restoredMac source input) =
            prefixKeysOn ran.2.1 source.publicValue (restoredBits source input)
              (restoredMac source input) := keysSame
        rw [sameKeys]
        exact encExact_of_enc (programAllSkip_enc _ _) encExact
      exact shadow_reveal_le scalar source input coins delta _ stored exact

open Classical in
/-- **(B2), on the curve, at the honest constant.** -/
theorem onCurve_reveal_bound (scalar : NonZeroScalar) (off : OffShadow) (source : Stage1Source)
    (input : AffineInput) (target : Point) :
    ∑' o, privateStage2U uniformMaskTape (planBShadow scalar off) scalar source input (some target) o *
        revealWeight o ≤ ENNReal.ofReal Kriterion.ArgoMAC.Phase3.Glue.exceptionalError := by
  let : Fintype Coins := Fintype.ofFinite Coins
  set a : ℝ≥0∞ := 91 * (Fintype.card Point : ℝ≥0∞)⁻¹ with aDef
  have bound := onCurve_reveal_le scalar off source input target
  -- swap the coins and the collision sets
  have swap : ∑' coins, PMF.uniformOfFintype Coins coins *
        ∑ T ∈ (Finset.univ : Finset EncPRF.PermutationIndex).powerset,
          epsPad ^ T.card * ind (∃ o, DiffersOn scalar coins.offsets (restoredBits source input) T o)
      = ∑ T ∈ (Finset.univ : Finset EncPRF.PermutationIndex).powerset, epsPad ^ T.card *
          ∑' coins, PMF.uniformOfFintype Coins coins *
            ind (∃ o, DiffersOn scalar coins.offsets (restoredBits source input) T o) := by
    simp_rw [Finset.mul_sum]
    rw [Summable.tsum_finsetSum fun _ _ => ENNReal.summable]
    refine Finset.sum_congr rfl fun T _ => ?_
    rw [← ENNReal.tsum_mul_left]
    refine tsum_congr fun coins => ?_
    ring
  rw [swap] at bound
  -- multiply by `1 − a`
  have aSmall : a ≠ ⊤ := ENNReal.mul_ne_top (by norm_num) (ENNReal.inv_ne_top.mpr (by
    have : 0 < Fintype.card Point := Fintype.card_pos
    exact_mod_cast this.ne'))
  have order := Kriterion.ArgoMAC.Security.Phase3.scalarFieldModulus_le_card_point
  have aLtOne : a < 1 := by
    rw [aDef, ← div_eq_mul_inv, ENNReal.div_lt_iff (Or.inl (by
      have : 0 < Fintype.card Point := Fintype.card_pos
      exact_mod_cast this.ne')) (Or.inl (ENNReal.natCast_ne_top _)), one_mul]
    have : 91 < Fintype.card Point := lt_of_lt_of_le (by norm_num [scalarFieldModulus]) order
    exact_mod_cast this
  have factorPos : 1 - a ≠ 0 := (tsub_pos_of_lt aLtOne).ne'
  have factorTop : 1 - a ≠ ⊤ := ENNReal.sub_ne_top ENNReal.one_ne_top
  have product : (∑ T ∈ (Finset.univ : Finset EncPRF.PermutationIndex).powerset, epsPad ^ T.card *
        ∑' coins, PMF.uniformOfFintype Coins coins *
          ind (∃ o, DiffersOn scalar coins.offsets (restoredBits source input) T o)) * (1 - a)
      ≤ (epsPad + 1) ^ 508 * a := by
    rw [Finset.sum_mul]
    calc ∑ T ∈ (Finset.univ : Finset EncPRF.PermutationIndex).powerset, epsPad ^ T.card *
          (∑' coins, PMF.uniformOfFintype Coins coins *
            ind (∃ o, DiffersOn scalar coins.offsets (restoredBits source input) T o)) * (1 - a)
        ≤ ∑ T ∈ (Finset.univ : Finset EncPRF.PermutationIndex).powerset, epsPad ^ T.card * a :=
          Finset.sum_le_sum fun T _ => by
            rw [mul_assoc]
            exact mul_le_mul' le_rfl (coins_differ_mul_le scalar (restoredBits source input) T)
      _ = (epsPad + 1) ^ 508 * a := by
          rw [← Finset.sum_mul]
          congr 1
          have := Finset.sum_pow_mul_eq_add_pow epsPad 1
            (Finset.univ : Finset EncPRF.PermutationIndex)
          simp only [one_pow, mul_one] at this
          rw [this]
          congr 1
  have final := le_trans (mul_le_mul' bound le_rfl) (le_trans product reveal_numeric)
  exact (ENNReal.mul_le_mul_iff_left factorPos factorTop).mp final

open Classical in
/-- **(B2) for `planBShadow`**: the reveal mass is `≤ 182/(r − 1)` on the curve, for every
off-curve part within the same budget off the curve. -/
theorem revealBound_planBShadow (scalar : NonZeroScalar) (off : OffShadow)
    (offBound : OffRevealBound off (ENNReal.ofReal Kriterion.ArgoMAC.Phase3.Glue.exceptionalError)) :
    RevealBound (planBShadow scalar off) scalar
      (ENNReal.ofReal Kriterion.ArgoMAC.Phase3.Glue.exceptionalError) := by
  intro source input
  cases output : Scheme.scheme.function scalar input with
  | none =>
    rw [privateStage2U_off]
    exact offBound source input
  | some target => exact onCurve_reveal_bound scalar off source input target

end Assembly

end

end Kriterion.ArgoMAC.Security.Phase3.PublicFirst
