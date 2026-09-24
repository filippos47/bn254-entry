/-
**Phase 3, P1, theorem 1 — the `G0 → G0U` swap of every garbler switch-mask vector.**

`B-output-aware-simulator.md` §1.5, `B-review.md` (3), and the phase-4 batched sampler
(`A1-batched-sampler-design.md` §1.3, §3): before anything else, the proof replaces **every**
garbler switch-mask vector — all four lanes, all `56` chunks, all `2 ^ b_c` switches of each chunk:
`1,396` vectors per lane, `5,584` in all (`card_vectorSite`) — by an independent uniform vector of
`F_p ^ laneCount lane`. The swap is **non-adaptive**: it is a statement about the whole tape, made
before stage 1, and it never mentions the adversary's input or which vectors it will later be
unable to compute.

### The sampler being swapped

The garbler's vector at the site `(ℓ, c, j)` is `PlanB.switchMask`: the `laneCount ℓ` base-`p`
digits (`sampleLane`) of the `limbCount ℓ` hash answers at `scaleInput ℓ c j i L`,
`i < limbCount ℓ`, where `L` is the switch's one-hot label.

### The tape, and the two laws

The hash oracle is split at the **scale range** `[0, 2 ^ 150)` (`hashSplit`) into its restriction
to the range (`ScaleTable`) and the rest (`OtherTable`). Every scale input lies in the range
(`scaleInput_val_lt_scaleRange`); the one other hash input the construction asks, the bridge input
`bridgeInput t`, lies outside it (`scaleRange_le_bridgeInput_val`); the `bin-to-hot` fold and the
gadget read the fixed-key oracle. So the one-hot labels are a function of the **rest** of the tape
(the coins, the fixed-key and EncPRF oracles, and the hash table off the range), and at those
labels the garbler reads the scale table at `Σ_ℓ 1396 · limbCount ℓ = 1,020,476` pairwise distinct
points (`limbInput_injective`, from `scaleInput_injective`).

* `realTape coinsLaw` — the coins, independent of a uniform hash oracle. This is the eager tape of
  the real game, restricted to its hash oracle.
* `swappedTape coinsLaw label` — the same, except that the scale table is drawn by `swapKernel`
  at the points the labels name: first the `5,584` vectors, iid uniform; then the limbs at the
  points uniformly among those that make these vectors (`fibreLaw masksOf`, jointly the product of
  the per-vector fibres `{h : sampleLane n k h = Y}`); every other entry of the scale table
  uniform, untouched.

### The theorem

`maskSwap_etvDist_le`: for **every** coin law, **every** label function and **every** observation
of the tape,

```
d( realTape.map observe , swappedTape.map observe )  ≤  Σ_site laneDelta site.lane
                                                     =  1396 · Σ_lane laneDelta lane
```

(`sum_vectorSite_laneDelta`), which is the Glue's `maskSwapError` (`GameSwap.maskSwapError_eq`).

**The proof is data processing over the whole tape.** A uniform table is its values at the
(injective) points followed by a uniform table overwritten there (`uniform_eq_bind_extend`); the
values are "vectors from their pushforward, then limbs uniformly on the fibre"
(`uniform_eq_bind_fibreLaw`). Together: the real table is its vectors from the batched sampler's
law, then the shared kernel `fibreKernel` (`uniform_eq_bind_fibreKernel`), and `swapKernel` is
uniform vectors, then the same `fibreKernel`. So the distance is at most the distance of the two
vector laws (`PMF.etvDist_bind_right_le`), which is the batched sampler's bias paid once per vector
site (`masksOf_etvDist_le`, from `Basic.sampleLane_etvDist_le`). The points enter only through a
shared first draw (`etvDist_bind_left_le_const`). No vector is ever singled out.

`swappedTape_switchMasks`: under the swapped tape the construction's own vectors at the labels —
`PlanB.switchMask` at every site — are iid uniform and independent of the rest of the tape. This is
the exact sense in which "every garbler switch-mask vector is replaced by an independent uniform
vector".
-/

import Proof.Privacy.Phase3.Basic
import Construction.ArgoMAC.Pipeline

set_option maxRecDepth 8000
set_option linter.unusedSectionVars false

namespace Kriterion.ArgoMAC.Security.Phase3

open BN254 Cryptography Kriterion.ArgoMAC.PlanB
open Kriterion.ArgoMAC.Security.PGS (uniformOfFintype_map_equiv)
open scoped ENNReal

noncomputable section

/-! ## Part 1 — lane vectors read off a hash table at injective points -/

section Generic

/-- The limb slots of a family of lane vectors: vector `v` asks `limbCount (laneOf v)` limbs. -/
abbrev LimbSlot {V : Type} (laneOf : V → Lane) := Σ v : V, Fin (limbCount (laneOf v))

/-- A family of lane vectors: vector `v` has the `laneCount (laneOf v)` coordinates of its lane. -/
abbrev LaneVectors {V : Type} (laneOf : V → Lane) :=
  (v : V) → Fin (laneCount (laneOf v)) → BaseField

variable {V : Type} [Fintype V] [DecidableEq V]

/-- **The batched sampler at every vector**: `sampleLane` of the vector's own limbs, exactly the
body of `PlanB.switchMask`. -/
def masksOf (laneOf : V → Lane) (values : LimbSlot laneOf → Block × Block) :
    LaneVectors laneOf :=
  fun v => sampleLane (laneCount (laneOf v)) (limbCount (laneOf v)) fun limb => values ⟨v, limb⟩

/-- The limbs of a family of lane vectors, grouped by vector (`Equiv.piCurry`). -/
def slotCurry (laneOf : V → Lane) :
    (LimbSlot laneOf → Block × Block) ≃ ∀ v, Fin (limbCount (laneOf v)) → Block × Block :=
  Equiv.piCurry fun v (_ : Fin (limbCount (laneOf v))) => Block × Block

/-- Every lane's limbs reach every vector of the lane: `254 · laneCount ≤ 256 · limbCount`. -/
theorem laneFits (lane : Lane) : 254 * laneCount lane ≤ 256 * limbCount lane := by
  cases lane <;> decide

/-- Every family of lane vectors is made by some limbs. -/
theorem masksOf_surjective (laneOf : V → Lane) : Function.Surjective (masksOf laneOf) := by
  intro vectors
  have each : ∀ v, ∃ limbs : Fin (limbCount (laneOf v)) → Block × Block,
      sampleLane (laneCount (laneOf v)) (limbCount (laneOf v)) limbs = vectors v :=
    fun v => sampleLane_surjective_of_le _ _ (laneFits (laneOf v)) (vectors v)
  choose limbs hLimbs using each
  exact ⟨fun slot => limbs slot.1 slot.2, funext hLimbs⟩

/-- Each lane's proof bias is `sampleLane`'s at the lane's `(laneCount, limbCount)`. -/
theorem laneDelta_eq (lane : Lane) :
    laneDelta lane = sampleLaneDelta (laneCount lane) (limbCount lane) := by
  cases lane <;> rfl

/-- **The batched sampler's bias, once per vector.** Uniform limbs make a family of lane vectors
within `Σ_v laneDelta (laneOf v)` of the uniform family. -/
theorem masksOf_etvDist_le (laneOf : V → Lane) :
    ((PMF.uniformOfFintype (LimbSlot laneOf → Block × Block)).map (masksOf laneOf)).etvDist
        (PMF.uniformOfFintype (LaneVectors laneOf))
      ≤ ∑ v, laneDelta (laneOf v) := by
  have curry : (PMF.uniformOfFintype (LimbSlot laneOf → Block × Block)).map (slotCurry laneOf)
      = PMF.uniformOfFintype (∀ v, Fin (limbCount (laneOf v)) → Block × Block) :=
    uniformOfFintype_map_equiv _
  have factor : masksOf laneOf
      = (fun family v => sampleLane (laneCount (laneOf v)) (limbCount (laneOf v)) (family v))
        ∘ slotCurry laneOf := rfl
  rw [factor, ← PMF.map_comp, curry]
  exact etvDist_dpi_map_uniform_le (fun v => Fin (limbCount (laneOf v)) → Block × Block)
    (fun v => Fin (laneCount (laneOf v)) → BaseField)
    (fun v => sampleLane (laneCount (laneOf v)) (limbCount (laneOf v)))
    (fun v => laneDelta (laneOf v))
    fun v => (sampleLane_etvDist_le_delta _ _).trans (laneDelta_eq (laneOf v)).ge

variable {laneOf : V → Lane} {D : Type} [Fintype D] [DecidableEq D]

/-- The table read at the points. -/
def evalAt (point : LimbSlot laneOf ↪ D) (table : D → Block × Block) :
    LimbSlot laneOf → Block × Block :=
  fun slot => table (point slot)

/-- The vectors a table makes at the points. -/
def maskMap (point : LimbSlot laneOf ↪ D) (table : D → Block × Block) : LaneVectors laneOf :=
  masksOf laneOf (evalAt point table)

/-- Overwriting a table at the points (`Function.extend`) leaves exactly the written values
there. -/
theorem evalAt_extend (point : LimbSlot laneOf ↪ D) (values : LimbSlot laneOf → Block × Block)
    (table : D → Block × Block) : evalAt point (Function.extend point values table) = values :=
  funext fun slot => point.injective.extend_apply values table slot

/-- Overwriting at the points and reading back at the points gives the written values. -/
theorem extend_comp_point {L : Type} (point : L ↪ D) (values : L → Block × Block)
    (table : D → Block × Block) : Function.extend point values table ∘ point = values :=
  funext fun slot => point.injective.extend_apply values table slot

/-- Rewriting the values at the points to a target's own values there, over a table that already
agrees with the target off the points, gives the target. -/
theorem extend_retarget {L : Type} (point : L ↪ D) (target table : D → Block × Block) :
    Function.extend point (target ∘ point) (Function.extend point (table ∘ point) target)
      = target := by
  funext input
  by_cases hit : ∃ slot, point slot = input
  · obtain ⟨slot, rfl⟩ := hit
    exact point.injective.extend_apply _ _ slot
  · rw [Function.extend_apply' _ _ _ hit, Function.extend_apply' _ _ _ hit]

/-- The fibre of `(values, table) ↦ Function.extend point values table` over `target`: the values
are the target's at the points, and the table agrees with the target off the points. -/
theorem extend_fibre {L : Type} (point : L ↪ D) {values : L → Block × Block}
    {table target : D → Block × Block} (hit : Function.extend point values table = target) :
    values = target ∘ point ∧ Function.extend point (table ∘ point) target = table := by
  refine ⟨?_, ?_⟩
  · rw [← hit, extend_comp_point]
  · funext input
    by_cases onPoint : ∃ slot, point slot = input
    · obtain ⟨slot, rfl⟩ := onPoint
      exact point.injective.extend_apply _ _ slot
    · rw [Function.extend_apply' _ _ _ onPoint, ← hit, Function.extend_apply' _ _ _ onPoint]

/-- Any two fibres of `(values, table) ↦ Function.extend point values table` are in bijection:
keep the table's values at the points, take everything else from the new target. -/
def extendFibreShift {L : Type} (point : L ↪ D) (first second : D → Block × Block) :
    {pair : (L → Block × Block) × (D → Block × Block) //
        Function.extend point pair.1 pair.2 = first}
      ≃ {pair : (L → Block × Block) × (D → Block × Block) //
        Function.extend point pair.1 pair.2 = second} where
  toFun pair := ⟨(second ∘ point, Function.extend point (pair.1.2 ∘ point) second),
    extend_retarget point second pair.1.2⟩
  invFun pair := ⟨(first ∘ point, Function.extend point (pair.1.2 ∘ point) first),
    extend_retarget point first pair.1.2⟩
  left_inv pair := by
    obtain ⟨⟨values, table⟩, hit⟩ := pair
    obtain ⟨hValues, hTable⟩ := extend_fibre (values := values) (table := table) point hit
    refine Subtype.ext ?_
    show (first ∘ point,
        Function.extend point (Function.extend point (table ∘ point) second ∘ point) first)
      = (values, table)
    rw [extend_comp_point, hTable, hValues]
  right_inv pair := by
    obtain ⟨⟨values, table⟩, hit⟩ := pair
    obtain ⟨hValues, hTable⟩ := extend_fibre (values := values) (table := table) point hit
    refine Subtype.ext ?_
    show (second ∘ point,
        Function.extend point (Function.extend point (table ∘ point) first ∘ point) second)
      = (values, table)
    rw [extend_comp_point, hTable, hValues]

/-- **A uniform table is its values at the points, then the rest.** For injective points, drawing
the table uniformly is drawing its values at the points uniformly and then a uniform table
overwritten there by them. -/
theorem uniform_eq_bind_extend {L : Type} [Fintype L] [DecidableEq L] (point : L ↪ D) :
    PMF.uniformOfFintype (D → Block × Block)
      = (PMF.uniformOfFintype (L → Block × Block)).bind fun values =>
          (PMF.uniformOfFintype (D → Block × Block)).map (Function.extend point values) := by
  have pushed : (PMF.uniformOfFintype ((L → Block × Block) × (D → Block × Block))).map
      (fun pair => Function.extend point pair.1 pair.2)
      = PMF.uniformOfFintype (D → Block × Block) :=
    uniform_map_of_fibre_equiv _ (extendFibreShift point)
  refine pushed.symm.trans ?_
  rw [uniformOfFintype_productPMF, productPMF, PMF.map_bind]
  refine congrArg _ (funext fun values => ?_)
  rw [PMF.map_comp]
  rfl

/-- **The kernel both tapes share given the vectors**: the limbs at the points uniformly among
those that make the vectors (`fibreLaw masksOf`, the product of the per-vector fibres
`{h : sampleLane n k h = Y}`), every other table entry uniform. -/
def fibreKernel (point : LimbSlot laneOf ↪ D) (vectors : LaneVectors laneOf) :
    PMF (D → Block × Block) :=
  (fibreLaw (masksOf laneOf) (masksOf_surjective laneOf) vectors).bind fun values =>
    (PMF.uniformOfFintype (D → Block × Block)).map (Function.extend point values)

/-- **The real table is its vectors, then the shared kernel**: the vectors from their (biased)
pushforward `(uniform limbs).map masksOf`, then `fibreKernel`. -/
theorem uniform_eq_bind_fibreKernel (point : LimbSlot laneOf ↪ D) :
    PMF.uniformOfFintype (D → Block × Block)
      = ((PMF.uniformOfFintype (LimbSlot laneOf → Block × Block)).map (masksOf laneOf)).bind
          (fibreKernel point) := by
  conv_lhs => rw [uniform_eq_bind_extend point, uniform_eq_bind_fibreLaw (masksOf laneOf)
    (masksOf_surjective laneOf), PMF.bind_bind]
  rfl

/-- **The swap kernel at a point set.** The vectors are drawn iid uniform; then the shared kernel:
the limbs at the points uniformly among those that make them, every other table entry uniform. -/
def swapKernel (point : LimbSlot laneOf ↪ D) : PMF (D → Block × Block) :=
  (PMF.uniformOfFintype (LaneVectors laneOf)).bind (fibreKernel point)

/-- **The per-point-set swap.** The uniform table and the swap kernel share the kernel given the
vectors; only the vector law differs. -/
theorem swapKernel_etvDist_le (point : LimbSlot laneOf ↪ D) :
    (PMF.uniformOfFintype (D → Block × Block)).etvDist (swapKernel point)
      ≤ ∑ v, laneDelta (laneOf v) := by
  rw [uniform_eq_bind_fibreKernel point, swapKernel]
  exact le_trans (PMF.etvDist_bind_right_le _ _ _) (masksOf_etvDist_le laneOf)

/-- Under the shared kernel the values at the points are uniform on the vectors' fibre. -/
theorem fibreKernel_evalAt (point : LimbSlot laneOf ↪ D) (vectors : LaneVectors laneOf) :
    (fibreKernel point vectors).map (evalAt point)
      = fibreLaw (masksOf laneOf) (masksOf_surjective laneOf) vectors := by
  rw [fibreKernel, PMF.map_bind]
  conv_rhs => rw [← PMF.bind_pure (fibreLaw (masksOf laneOf) (masksOf_surjective laneOf) vectors)]
  refine congrArg _ (funext fun values => ?_)
  rw [PMF.map_comp]
  have constant : evalAt point ∘ Function.extend point values = Function.const _ values :=
    funext fun table => evalAt_extend point values table
  rw [constant]
  exact PMF.map_const _ values

/-- The shared kernel makes exactly the given vectors. -/
theorem fibreKernel_masks (point : LimbSlot laneOf ↪ D) (vectors : LaneVectors laneOf) :
    (fibreKernel point vectors).map (maskMap point) = PMF.pure vectors := by
  have factor : maskMap point = masksOf laneOf ∘ evalAt point := rfl
  rw [factor, ← PMF.map_comp, fibreKernel_evalAt]
  exact fibreLaw_map (masksOf laneOf) (masksOf_surjective laneOf) vectors

/-- **Under the swap kernel the vectors are exactly iid uniform.** -/
theorem swapKernel_masks (point : LimbSlot laneOf ↪ D) :
    (swapKernel point).map (maskMap point) = PMF.uniformOfFintype (LaneVectors laneOf) := by
  rw [swapKernel, PMF.map_bind]
  conv_rhs => rw [← PMF.bind_pure (PMF.uniformOfFintype (LaneVectors laneOf))]
  exact congrArg _ (funext (fibreKernel_masks point))

/-! ### The whole tape -/

variable {Rest : Type}

/-- **`G0`.** The rest of the tape under any law; the table uniform and independent. -/
def realLaw (restLaw : PMF Rest) : PMF (Rest × (D → Block × Block)) :=
  restLaw.bind fun rest => (PMF.uniformOfFintype (D → Block × Block)).map (Prod.mk rest)

/-- **`G0U`.** The same rest; the table from the swap kernel at the points the rest determines. -/
def swapLaw (restLaw : PMF Rest) (point : Rest → (LimbSlot laneOf ↪ D)) :
    PMF (Rest × (D → Block × Block)) :=
  restLaw.bind fun rest => (swapKernel (point rest)).map (Prod.mk rest)

/-- **The swap over the whole tape.** For every law of the rest, every point function and every
observation, the two tapes are `Σ_v laneDelta (laneOf v)`-close. -/
theorem swap_etvDist_le {X : Type} (restLaw : PMF Rest) (point : Rest → (LimbSlot laneOf ↪ D))
    (observe : Rest × (D → Block × Block) → X) :
    ((realLaw restLaw).map observe).etvDist ((swapLaw restLaw point).map observe)
      ≤ ∑ v, laneDelta (laneOf v) := by
  rw [realLaw, swapLaw, PMF.map_bind, PMF.map_bind]
  refine etvDist_bind_left_le_const restLaw _ _ _ fun rest => ?_
  rw [PMF.map_comp, PMF.map_comp]
  exact le_trans (etvDist_map_le' _ _ _) (swapKernel_etvDist_le (point rest))

/-- **Under `G0U` the vectors are iid uniform and independent of the rest.** -/
theorem swapLaw_masks (restLaw : PMF Rest) (point : Rest → (LimbSlot laneOf ↪ D)) :
    (swapLaw restLaw point).map (fun tape => (tape.1, maskMap (point tape.1) tape.2))
      = productPMF restLaw (PMF.uniformOfFintype (LaneVectors laneOf)) := by
  rw [swapLaw, PMF.map_bind, productPMF]
  refine congrArg _ (funext fun rest => ?_)
  rw [PMF.map_comp]
  have factor : ((fun tape : Rest × (D → Block × Block) => (tape.1, maskMap (point tape.1) tape.2))
      ∘ Prod.mk rest) = Prod.mk rest ∘ maskMap (point rest) := rfl
  rw [factor, ← PMF.map_comp, swapKernel_masks]

/-! ### One vector site at a time

Given all the vectors, the limbs of distinct sites are independent, each uniform on its own fibre
`{h : sampleLane n k h = Y}` (`fibreLaw_masksOf_eq`). One site's limbs given its vector have the
law `siteFibreLaw`, and its swapped limbs the law `siteSwapLaw` ("the vector uniform, then its
limbs on its fibre"); `PublicFirst/LawsOnEFibre.lean` reads the designated site through them. -/

/-- **One vector's limbs given the vector**: uniform on its own fibre
`{h : sampleLane n k h = Y}`. -/
def siteFibreLaw (lane : Lane) (vector : Fin (laneCount lane) → BaseField) :
    PMF (Fin (limbCount lane) → Block × Block) :=
  fibreLaw (sampleLane (laneCount lane) (limbCount lane))
    (sampleLane_surjective_of_le _ _ (laneFits lane)) vector

/-- **One vector site's swapped limbs**: the vector uniform, then its limbs uniform on its
fibre. -/
def siteSwapLaw (lane : Lane) : PMF (Fin (limbCount lane) → Block × Block) :=
  (PMF.uniformOfFintype (Fin (laneCount lane) → BaseField)).bind (siteFibreLaw lane)

/-- Two maps that agree on a fibre push its uniform law to the same law. -/
theorem fibreLaw_map_congr {A B C : Type} [Fintype A] [DecidableEq B] (g : A → B)
    (onto : Function.Surjective g) (target : B) {first second : A → C}
    (agree : ∀ x, g x = target → first x = second x) :
    (fibreLaw g onto target).map first = (fibreLaw g onto target).map second := by
  unfold fibreLaw
  rw [PMF.map_comp, PMF.map_comp]
  exact congrArg (fun map => PMF.map map _) (funext fun x => agree x.1 x.2)

/-- The batched sampler's fibre is the product of the per-vector fibres. -/
def masksOfFibreEquiv (laneOf : V → Lane) (vectors : LaneVectors laneOf) :
    {values : LimbSlot laneOf → Block × Block // masksOf laneOf values = vectors}
      ≃ ∀ v, {limbs : Fin (limbCount (laneOf v)) → Block × Block //
          sampleLane (laneCount (laneOf v)) (limbCount (laneOf v)) limbs = vectors v} where
  toFun values v := ⟨fun limb => values.1 ⟨v, limb⟩, congrFun values.2 v⟩
  invFun limbs := ⟨fun slot => (limbs slot.1).1 slot.2, funext fun v => (limbs v).2⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- **Given all the vectors, the limbs of distinct vector sites are independent, each uniform on
its own fibre** `{h : sampleLane n k h = Y_v}`. -/
theorem fibreLaw_masksOf_eq (laneOf : V → Lane) (vectors : LaneVectors laneOf) :
    fibreLaw (masksOf laneOf) (masksOf_surjective laneOf) vectors
      = (piPMF fun v => siteFibreLaw (laneOf v) (vectors v)).map (slotCurry laneOf).symm := by
  have : ∀ v, Nonempty {limbs : Fin (limbCount (laneOf v)) → Block × Block //
      sampleLane (laneCount (laneOf v)) (limbCount (laneOf v)) limbs = vectors v} := fun v =>
    ⟨⟨_, Classical.choose_spec
      (sampleLane_surjective_of_le _ _ (laneFits (laneOf v)) (vectors v))⟩⟩
  have : Nonempty {values : LimbSlot laneOf → Block × Block // masksOf laneOf values = vectors} :=
    ⟨(masksOfFibreEquiv laneOf vectors).symm fun _ => Classical.arbitrary _⟩
  have left : fibreLaw (masksOf laneOf) (masksOf_surjective laneOf) vectors
      = (PMF.uniformOfFintype (∀ v, {limbs : Fin (limbCount (laneOf v)) → Block × Block //
          sampleLane (laneCount (laneOf v)) (limbCount (laneOf v)) limbs = vectors v})).map
        (Subtype.val ∘ (masksOfFibreEquiv laneOf vectors).symm) := by
    rw [← PMF.map_comp, uniformOfFintype_map_equiv]
    rfl
  have right : (piPMF fun v => siteFibreLaw (laneOf v) (vectors v))
      = (PMF.uniformOfFintype (∀ v, {limbs : Fin (limbCount (laneOf v)) → Block × Block //
          sampleLane (laneCount (laneOf v)) (limbCount (laneOf v)) limbs = vectors v})).map
        (fun family v => (family v).1) := by
    rw [uniform_pi_eq_piPMF, piPMF_map]
    rfl
  rw [left, right, PMF.map_comp]
  rfl

end Generic

/-! ## Part 2 — the Plan B vector sites -/

/-- **A garbler switch-mask vector site**: a lane, a chunk, and a switch of that chunk. The
garbler draws one vector `Y_{ℓ,c,j} ∈ F_p ^ laneCount ℓ` per site (`PlanB.switchMask`), from
`limbCount ℓ` hash limbs; its coordinates are `e : Fin (laneCount site.lane)` (`MaskCoord`). -/
structure VectorSite where
  /-- The lane of the switch system. -/
  lane : Lane
  /-- The chunk. -/
  chunk : Fin chunkCount
  /-- The switch, one of the chunk's `2 ^ chunkWidth chunk`. -/
  switch : Fin (2 ^ chunkWidth chunk)
  deriving DecidableEq

/-- A vector site is a (lane, chunk, switch) triple. -/
def vectorSiteEquiv :
    VectorSite ≃ Σ _lane : Lane, Σ chunk : Fin chunkCount, Fin (2 ^ chunkWidth chunk) where
  toFun site := ⟨site.lane, site.chunk, site.switch⟩
  invFun triple := ⟨triple.1, triple.2.1, triple.2.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

instance : Fintype VectorSite := Fintype.ofEquiv _ vectorSiteEquiv.symm

/-- A sum over the vector sites is a sum over lanes, chunks and switches. -/
theorem sum_vectorSite {M : Type} [AddCommMonoid M] (f : VectorSite → M) :
    ∑ site, f site
      = ∑ lane : Lane, ∑ chunk : Fin chunkCount, ∑ switch : Fin (2 ^ chunkWidth chunk),
          f ⟨lane, chunk, switch⟩ := by
  rw [← Fintype.sum_equiv vectorSiteEquiv.symm (fun triple => f (vectorSiteEquiv.symm triple)) f
    fun _ => rfl, Fintype.sum_sigma]
  refine Finset.sum_congr rfl fun lane _ => ?_
  rw [Fintype.sum_sigma]
  rfl

/-- `Σ_c 2 ^ b_c = 4 + 32 · 32 + 23 · 16 = 1,396` at the ragged-first profile, from the generic
chunk sum `Params.sum_chunkWidth`: the number of switch vectors of one lane. It is
`Glue.laneVectorCount` (`GameSwap.laneVectorCount_eq`). -/
theorem sum_twoPow_chunkWidth : ∑ chunk : Fin chunkCount, 2 ^ chunkWidth chunk = 1396 := by
  rw [sum_chunkWidth (fun width => 2 ^ width)]
  rfl

/-- **Every lane has `1,396` vector sites**: a sum over the sites of a function of the lane is
`1396 •` its sum over the lanes. -/
theorem sum_vectorSite_lane {M : Type} [AddCommMonoid M] (f : Lane → M) :
    ∑ site : VectorSite, f site.lane = ∑ lane : Lane, 1396 • f lane := by
  rw [sum_vectorSite]
  refine Finset.sum_congr rfl fun lane _ => ?_
  rw [← sum_twoPow_chunkWidth, Finset.sum_smul]
  refine Finset.sum_congr rfl fun chunk _ => ?_
  show ∑ _switch : Fin (2 ^ chunkWidth chunk), f lane = _
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin]

/-- **`#VectorSite = 5,584`**: `4` lanes, `1,396` vectors each. -/
theorem card_vectorSite : Fintype.card VectorSite = 5584 := by
  have lanes := sum_vectorSite_lane (M := ℕ) fun _ => 1
  rw [Fintype.card_eq_sum_ones, lanes, Finset.sum_const, Finset.card_univ, card_lane]
  rfl

/-- **The whole swap bias**: `Σ_site laneDelta site.lane = 1396 · Σ_lane laneDelta lane`. -/
theorem sum_vectorSite_laneDelta :
    ∑ site : VectorSite, laneDelta site.lane = 1396 * ∑ lane : Lane, laneDelta lane := by
  rw [sum_vectorSite_lane, Finset.mul_sum]
  refine Finset.sum_congr rfl fun lane _ => ?_
  rw [nsmul_eq_mul, Nat.cast_ofNat]

/-- The Plan B limb slots: `limbCount lane` hash limbs per vector site. -/
abbrev LimbSite := LimbSlot VectorSite.lane

/-- The Plan B mask vectors: one `F_p ^ laneCount lane` vector per vector site. -/
abbrev MaskVectors := LaneVectors VectorSite.lane

/-- One mask coordinate: a vector site and a coordinate `e` of its lane (the element slot
`Y_{ℓ,c,j}[e]`). -/
abbrev MaskCoord := Σ site : VectorSite, Fin (laneCount site.lane)

/-- The mask vectors as a flat family over the mask coordinates. -/
def maskCoordEquiv : MaskVectors ≃ (MaskCoord → BaseField) :=
  (Equiv.piCurry fun (site : VectorSite) (_ : Fin (laneCount site.lane)) => BaseField).symm

/-! ### The hash table, split at the scale range -/

/-- The scale range of hash inputs, `[0, 2 ^ 150)`: every scale input lies in it
(`scaleInput_val_lt_scaleRange`), the bridge input never does (`scaleRange_le_bridgeInput_val`). -/
abbrev ScaleInput := {input : BaseField // input.val < scaleRange}

/-- The hash inputs off the scale range. -/
abbrev OtherInput := {input : BaseField // ¬ input.val < scaleRange}

/-- The scale part of the hash table: every switch-mask limb the garbler asks. -/
abbrev ScaleTable := ScaleInput → Block × Block

/-- The rest of the hash table (the bridge input and every input no switch mask asks). -/
abbrev OtherTable := OtherInput → Block × Block

/-- Reassemble the hash oracle from its two parts. -/
def hashOf (other : OtherTable) (scale : ScaleTable) : EncPRF.HashOracle := fun input =>
  if low : input.val < scaleRange then scale ⟨input, low⟩ else other ⟨input, low⟩

theorem hashOf_scale (other : OtherTable) (scale : ScaleTable) (input : ScaleInput) :
    hashOf other scale input.1 = scale input :=
  dif_pos input.2

theorem hashOf_other (other : OtherTable) (scale : ScaleTable) (input : OtherInput) :
    hashOf other scale input.1 = other input :=
  dif_neg input.2

/-- The scale part of a hash oracle. -/
def scaleTableOf (hash : EncPRF.HashOracle) : ScaleTable := fun input => hash input.1

/-- The rest of a hash oracle. -/
def otherTableOf (hash : EncPRF.HashOracle) : OtherTable := fun input => hash input.1

theorem hashOf_tables (hash : EncPRF.HashOracle) :
    hashOf (otherTableOf hash) (scaleTableOf hash) = hash := by
  funext input
  by_cases low : input.val < scaleRange
  · exact hashOf_scale _ _ ⟨input, low⟩
  · exact hashOf_other _ _ ⟨input, low⟩

theorem otherTableOf_hashOf (other : OtherTable) (scale : ScaleTable) :
    otherTableOf (hashOf other scale) = other :=
  funext fun input => hashOf_other other scale input

theorem scaleTableOf_hashOf (other : OtherTable) (scale : ScaleTable) :
    scaleTableOf (hashOf other scale) = scale :=
  funext fun input => hashOf_scale other scale input

/-- The hash oracle, split at the scale range. -/
def hashSplit : EncPRF.HashOracle ≃ OtherTable × ScaleTable where
  toFun hash := (otherTableOf hash, scaleTableOf hash)
  invFun tables := hashOf tables.1 tables.2
  left_inv := hashOf_tables
  right_inv _ := Prod.ext (otherTableOf_hashOf _ _) (scaleTableOf_hashOf _ _)

/-- A uniform hash oracle is a uniform rest and an independent uniform scale table. -/
theorem uniform_hash_eq :
    PMF.uniformOfFintype EncPRF.HashOracle
      = (productPMF (PMF.uniformOfFintype OtherTable) (PMF.uniformOfFintype ScaleTable)).map
          fun tables => hashOf tables.1 tables.2 := by
  rw [← uniformOfFintype_productPMF]
  exact (uniformOfFintype_map_equiv hashSplit.symm).symm

/-- The bridge input is off the scale range. -/
theorem bridgeInput_not_lt (t : BaseField) : ¬ (bridgeInput t).val < scaleRange :=
  not_lt.mpr (scaleRange_le_bridgeInput_val t)

/-- **The bridge hash reads only the rest of the table.** -/
theorem hashOf_bridgeInput (other : OtherTable) (scale : ScaleTable) (t : BaseField) :
    hashOf other scale (bridgeInput t) = other ⟨bridgeInput t, bridgeInput_not_lt t⟩ :=
  hashOf_other other scale ⟨bridgeInput t, bridgeInput_not_lt t⟩

/-- The scale table left blank, for reading the rest of the table through `hashOf`. -/
def blankScale : ScaleTable := fun _ => (0, 0)

/-! ### The limb points -/

/-- **The hash input of a limb slot** at given one-hot labels: `scaleInput ℓ c j i L_{ℓ,c,j}`. -/
def limbInput (label : VectorSite → Block) (slot : LimbSite) : ScaleInput :=
  ⟨scaleInput slot.1.lane slot.1.chunk slot.1.switch.val slot.2.val (label slot.1),
    scaleInput_val_lt_scaleRange _ _ _ _ _⟩

/-- **One hash input per limb slot**, whatever the labels: the `1,020,476` inputs are pairwise
distinct (`scaleInput_injective`: distinct lanes, chunks, switches or limbs never share one). -/
theorem limbInput_injective (label : VectorSite → Block) :
    Function.Injective (limbInput label) := by
  rintro ⟨⟨lane, chunk, switch⟩, limb⟩ ⟨⟨lane', chunk', switch'⟩, limb'⟩ same
  obtain ⟨laneEq, chunkEq, switchEq, limbEq, -⟩ := scaleInput_injective
    (Pipeline.switch_lt_twoPowChunkBits chunk switch)
    (Pipeline.switch_lt_twoPowChunkBits chunk' switch')
    (lt_trans limb.isLt (limbCount_lt lane)) (lt_trans limb'.isLt (limbCount_lt lane'))
    (congrArg Subtype.val same)
  subst laneEq
  subst chunkEq
  obtain rfl : switch = switch' := Fin.ext switchEq
  obtain rfl : limb = limb' := Fin.ext limbEq
  rfl

/-- The limb points at given labels, as an embedding into the scale range. -/
def limbPoint (label : VectorSite → Block) : LimbSite ↪ ScaleInput :=
  ⟨limbInput label, limbInput_injective label⟩

/-! ### The real tape and the swapped tape -/

section Tape

variable {Coins : Type}

/-- The part of the tape the swap does not touch: the coins and the hash table off the range. -/
abbrev RestTape (Coins : Type) := Coins × OtherTable

/-- The scale table and the rest, put back together. -/
def assemble (tape : RestTape Coins × ScaleTable) : Coins × EncPRF.HashOracle :=
  (tape.1.1, hashOf tape.1.2 tape.2)

/-- The law of the rest when the hash oracle is uniform and independent of the coins. -/
def restLaw (coinsLaw : PMF Coins) : PMF (RestTape Coins) :=
  productPMF coinsLaw (PMF.uniformOfFintype OtherTable)

/-- **The real (eager) tape**: the coins, independent of a uniform hash oracle. -/
def realTape (coinsLaw : PMF Coins) : PMF (Coins × EncPRF.HashOracle) :=
  productPMF coinsLaw (PMF.uniformOfFintype EncPRF.HashOracle)

/-- **The swapped tape (`G0U`)**: the scale table drawn by the swap kernel at the limb points of
the labels the rest of the tape determines. -/
def swappedTape (coinsLaw : PMF Coins) (label : RestTape Coins → VectorSite → Block) :
    PMF (Coins × EncPRF.HashOracle) :=
  (swapLaw (restLaw coinsLaw) fun rest => limbPoint (label rest)).map assemble

/-- The real tape is `G0` on the split hash oracle. -/
theorem realTape_eq (coinsLaw : PMF Coins) :
    realTape coinsLaw = (realLaw (restLaw coinsLaw)).map assemble := by
  have left : realTape coinsLaw = coinsLaw.bind fun coins =>
      (PMF.uniformOfFintype OtherTable).bind fun other =>
        (PMF.uniformOfFintype ScaleTable).map fun scale => (coins, hashOf other scale) := by
    rw [realTape, uniform_hash_eq, productPMF, productPMF]
    refine congrArg _ (funext fun coins => ?_)
    rw [PMF.map_comp, PMF.map_bind]
    refine congrArg _ (funext fun other => ?_)
    rw [PMF.map_comp]
    rfl
  have right : (realLaw (restLaw coinsLaw)).map assemble = coinsLaw.bind fun coins =>
      (PMF.uniformOfFintype OtherTable).bind fun other =>
        (PMF.uniformOfFintype ScaleTable).map fun scale => (coins, hashOf other scale) := by
    rw [realLaw, restLaw, productPMF, PMF.bind_bind, PMF.map_bind]
    refine congrArg _ (funext fun coins => ?_)
    rw [PMF.bind_map, PMF.map_bind]
    refine congrArg _ (funext fun other => ?_)
    rw [Function.comp_apply, PMF.map_comp]
    rfl
  rw [left, right]

/-- **Theorem 1 (`G0 → G0U`), for every observation of the tape.** -/
theorem maskSwap_etvDist_le {X : Type} (coinsLaw : PMF Coins)
    (label : RestTape Coins → VectorSite → Block) (observe : Coins × EncPRF.HashOracle → X) :
    ((realTape coinsLaw).map observe).etvDist ((swappedTape coinsLaw label).map observe)
      ≤ ∑ site : VectorSite, laneDelta site.lane := by
  rw [realTape_eq, swappedTape, PMF.map_comp, PMF.map_comp]
  exact swap_etvDist_le (restLaw coinsLaw) (fun rest => limbPoint (label rest)) (observe ∘ assemble)

/-- **Theorem 1, as a game hop.** Any randomized continuation run on the tape — the garbler, the
adversary's two stages against the same oracle, the final bit — gains at most the swap bias. -/
theorem maskSwap_bind_etvDist_le {X : Type} (coinsLaw : PMF Coins)
    (label : RestTape Coins → VectorSite → Block)
    (game : Coins × EncPRF.HashOracle → PMF X) :
    ((realTape coinsLaw).bind game).etvDist ((swappedTape coinsLaw label).bind game)
      ≤ ∑ site : VectorSite, laneDelta site.lane := by
  refine le_trans (PMF.etvDist_bind_right_le game _ _) ?_
  have identity := maskSwap_etvDist_le coinsLaw label id
  rwa [PMF.map_id, PMF.map_id] at identity

end Tape

/-! ### The garbler's labels, and the garbler's vectors -/

/-- **The garbler's one-hot label at a vector site**: the switch's label from the lane's
`bin-to-hot` fold on the lane's bit keys. It reads the fixed-key oracle only. -/
def garblerLabel (fixed : PermutationOracle FixedIndex Block) (delta : Lane → Block)
    (bitKey : Lane → Fin PlanB.coordinateBits → Block × Block) (site : VectorSite) : Block :=
  (garbleChunk fixed site.lane (delta site.lane) (bitKey site.lane) site.chunk).1 site.switch

/-- **The construction's switch-mask vectors at given labels**: `PlanB.switchMask` at every site. -/
def switchMasks (hash : EncPRF.HashOracle) (label : VectorSite → Block) : MaskVectors :=
  fun site => switchMask hash site.lane site.chunk site.switch.val (label site)

/-- The construction's vectors are `maskMap` of the scale table at the labels' limb points. -/
theorem switchMasks_hashOf (other : OtherTable) (scale : ScaleTable) (label : VectorSite → Block) :
    switchMasks (hashOf other scale) label = maskMap (limbPoint label) scale := by
  funext site
  unfold switchMasks switchMask maskMap masksOf evalAt
  congr 1
  funext limb
  exact hashOf_scale other scale (limbInput label ⟨site, limb⟩)

/-- **Every garbler switch-mask vector, swapped.** Under `G0U`, for every label function of the
rest, the construction's vectors at those labels — every lane, chunk and switch — are iid uniform
and independent of the coins and of the rest of the hash table. -/
theorem swappedTape_switchMasks {Coins : Type} (coinsLaw : PMF Coins)
    (label : RestTape Coins → VectorSite → Block) :
    (swappedTape coinsLaw label).map
        (fun tape => ((tape.1, otherTableOf tape.2),
          switchMasks tape.2 (label (tape.1, otherTableOf tape.2))))
      = productPMF (restLaw coinsLaw) (PMF.uniformOfFintype MaskVectors) := by
  rw [swappedTape, PMF.map_comp,
    ← swapLaw_masks (restLaw coinsLaw) fun rest => limbPoint (label rest)]
  refine congrArg (fun observe => PMF.map observe
    (swapLaw (restLaw coinsLaw) fun rest => limbPoint (label rest))) (funext fun tape => ?_)
  obtain ⟨⟨coins, other⟩, scale⟩ := tape
  show ((coins, otherTableOf (hashOf other scale)),
      switchMasks (hashOf other scale) (label (coins, otherTableOf (hashOf other scale))))
    = ((coins, other), maskMap (limbPoint (label (coins, other))) scale)
  rw [otherTableOf_hashOf, switchMasks_hashOf]

/-- **The construction's garbler vectors**: `switchMask` at the garbler's own one-hot labels,
exactly as `PlanB.garbleScale` and `PlanB.outputMask` read them. -/
def garblerMask (fixed : PermutationOracle FixedIndex Block) (hash : EncPRF.HashOracle)
    (delta : Lane → Block) (bitKey : Lane → Fin PlanB.coordinateBits → Block × Block) :
    MaskVectors :=
  switchMasks hash (garblerLabel fixed delta bitKey)

/-- The Plan B label function: the garbler's one-hot labels, computed from the rest of the tape.
`fixed` reads the fixed-key oracle off the coins; `keys` reads each lane's global offset and bit
keys off the rest (the raw Lamport keys for system A, the EncPRF-whitened keys for system B, whose
`hash(bridgeInput t)` lies in the rest of the table). -/
def planBLabel {Coins : Type} (fixed : Coins → PermutationOracle FixedIndex Block)
    (keys : RestTape Coins → (Lane → Block) × (Lane → Fin PlanB.coordinateBits → Block × Block))
    (rest : RestTape Coins) : VectorSite → Block :=
  garblerLabel (fixed rest.1) (keys rest).1 (keys rest).2

/-- **Every garbler switch-mask vector, swapped** (the construction's vectors at the garbler's
own labels): under `G0U` they are iid uniform and independent of the rest of the tape. -/
theorem swappedTape_garblerMasks {Coins : Type} (coinsLaw : PMF Coins)
    (fixed : Coins → PermutationOracle FixedIndex Block)
    (keys : RestTape Coins → (Lane → Block) × (Lane → Fin PlanB.coordinateBits → Block × Block)) :
    (swappedTape coinsLaw (planBLabel fixed keys)).map
        (fun tape => ((tape.1, otherTableOf tape.2),
          garblerMask (fixed tape.1) tape.2 (keys (tape.1, otherTableOf tape.2)).1
            (keys (tape.1, otherTableOf tape.2)).2))
      = productPMF (restLaw coinsLaw) (PMF.uniformOfFintype MaskVectors) :=
  swappedTape_switchMasks coinsLaw (planBLabel fixed keys)

end

end Kriterion.ArgoMAC.Security.Phase3
