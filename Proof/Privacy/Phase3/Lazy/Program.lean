/-
**Phase 3, P4b — program-level tools for the per-prefix failure bound.**

* `FreeQuery` monad laws (`fq_bind_assoc`, `fq_pure_bind`) and **`vector_succ_first`**: a
  `FreeQuery.vector` runs its first iteration first, so chunk `0` of a lane can be split off.
* `AllQ P c`: every query of `c`, on every path, satisfies `P`; closed under `bind`, `vector`,
  `ite` and weakening.
* `IndexAt lane chunk`: the fixed-key (fold) indices of one (lane, chunk); `CellAt lane chunk`: the
  hash inputs of its cells. The per-chunk evaluator `evalChunkM` asks only forward fold queries and
  hash queries there (`evalChunkM_allQ`), the pads only EncPRF queries, the bridge only the hash.
-/

import Proof.Privacy.Phase3.Lazy.RunBind

set_option maxRecDepth 8000
set_option linter.unusedSectionVars false

namespace Kriterion.ArgoMAC.Phase3.Lazy

open BN254 Cryptography GarbledCircuit
open Kriterion.ArgoMAC.PlanB hiding coordinateBits
open Kriterion.ArgoMAC.Phase3.Glue

/-! ### Monad laws of `FreeQuery` -/

section Laws

variable {spec : OracleSpec.{0, 0}} {α β γ : Type}

theorem fq_bind_assoc (c : FreeQuery spec α) (f : α → FreeQuery spec β)
    (g : β → FreeQuery spec γ) : (c >>= f) >>= g = c >>= fun x => f x >>= g := by
  induction c with
  | pure value => rfl
  | query request next ih =>
      show FreeQuery.query request (fun answer => FreeQuery.bind (FreeQuery.bind (next answer) f) g)
        = FreeQuery.query request fun answer => FreeQuery.bind (next answer) fun x =>
          FreeQuery.bind (f x) g
      congr 1
      funext answer
      exact ih answer

theorem fq_pure_bind (a : α) (f : α → FreeQuery spec β) :
    (Pure.pure a : FreeQuery spec α) >>= f = f a := rfl

/-- A vector with a new first entry. -/
def vcons {n : Nat} (x : α) (v : Vector α n) : Vector α (n + 1) :=
  Vector.ofFn (Fin.cons (α := fun _ => α) x v.get)

theorem vget_eq {n : Nat} (v : Vector α n) (i : Fin n) : v.get i = v[i.val] := by
  simp [Vector.get]

theorem vcons_push {n : Nat} (x : α) (v : Vector α n) (y : α) :
    (vcons x v).push y = vcons x (v.push y) := by
  apply Vector.ext
  intro index bound
  rw [Vector.getElem_push]
  simp only [vcons, Vector.getElem_ofFn]
  split
  · rename_i small
    cases index with
    | zero => rfl
    | succ index =>
        show v.get ⟨index, by omega⟩ = (v.push y).get ⟨index, by omega⟩
        rw [vget_eq, vget_eq, Vector.getElem_push_lt]
  · rename_i large
    have last : index = n + 1 := by omega
    subst last
    show y = (v.push y).get ⟨n, by omega⟩
    rw [vget_eq, Vector.getElem_push_eq]

/-- **A vector runs its first iteration first.** -/
theorem vector_succ_first : ∀ (n : Nat) (f : Fin (n + 1) → FreeQuery spec α),
    FreeQuery.vector (n + 1) f =
      f 0 >>= fun x => FreeQuery.vector n (fun i => f i.succ) >>= fun v => Pure.pure (vcons x v)
  | 0, f => by
      show (Pure.pure #v[] : FreeQuery spec (Vector α 0)) >>= (fun values =>
        f (Fin.last 0) >>= fun value => Pure.pure (values.push value)) = _
      rw [fq_pure_bind]
      show f (Fin.last 0) >>= (fun value => Pure.pure (#v[].push value)) =
        f 0 >>= fun x => (Pure.pure #v[] : FreeQuery spec (Vector α 0)) >>= fun v =>
          Pure.pure (vcons x v)
      have last : (Fin.last 0 : Fin 1) = 0 := rfl
      rw [last]
      congr 1
  | n + 1, f => by
      show FreeQuery.vector (n + 1) (fun index => f index.castSucc) >>= (fun values =>
        f (Fin.last (n + 1)) >>= fun value => Pure.pure (values.push value)) = _
      rw [vector_succ_first n (fun index => f index.castSucc)]
      show _ = f 0 >>= fun x => (FreeQuery.vector n (fun index => f index.castSucc.succ) >>=
        fun values => f (Fin.last n).succ >>= fun value => Pure.pure (values.push value)) >>=
          fun v => Pure.pure (vcons x v)
      rw [fq_bind_assoc]
      have zero : (Fin.castSucc (0 : Fin (n + 1)) : Fin (n + 2)) = 0 := rfl
      rw [zero]
      congr 1
      funext x
      rw [fq_bind_assoc, fq_bind_assoc]
      have swap : (fun index : Fin n => f index.succ.castSucc) =
          fun index => f index.castSucc.succ := by
        funext index
        rw [Fin.succ_castSucc]
      rw [swap]
      congr 1
      funext v
      rw [fq_pure_bind, fq_bind_assoc, Fin.succ_last]
      congr 1
      funext y
      rw [fq_pure_bind, vcons_push]

end Laws

/-! ### A parametric query predicate -/

/-- **Every query of the program, on every path, satisfies `P`.** -/
inductive AllQ (P : Request → Prop) {α : Type} : FreeQuery Programs.Spec α → Prop
  | pure (value : α) : AllQ P (.pure value)
  | query (request : Request) (next : request.Answer → FreeQuery Programs.Spec α) :
      P request → (∀ answer, AllQ P (next answer)) → AllQ P (.query request next)

namespace AllQ

variable {P Q : Request → Prop} {α β : Type}

theorem bind {c : FreeQuery Programs.Spec α} (first : AllQ P c)
    {f : α → FreeQuery Programs.Spec β} (rest : ∀ value, AllQ P (f value)) :
    AllQ P (c >>= f) := by
  induction first with
  | pure value => exact rest value
  | query request next holds _ ih => exact .query request _ holds ih

theorem pure' (value : α) : AllQ P (Pure.pure value : FreeQuery Programs.Spec α) := .pure value

theorem vector {count : Nat} {program : Fin count → FreeQuery Programs.Spec α}
    (each : ∀ index, AllQ P (program index)) : AllQ P (FreeQuery.vector count program) := by
  induction count with
  | zero => exact .pure _
  | succ count ih =>
      exact bind (ih fun index => each index.castSucc) fun _ =>
        bind (each (Fin.last count)) fun _ => pure' _

theorem ite {condition : Prop} [Decidable condition] {first second : FreeQuery Programs.Spec α}
    (yes : AllQ P first) (no : AllQ P second) :
    AllQ P (if condition then first else second) := by
  split
  · exact yes
  · exact no

theorem mono {c : FreeQuery Programs.Spec α} (holds : AllQ P c) (weaker : ∀ r, P r → Q r) :
    AllQ Q c := by
  induction holds with
  | pure value => exact .pure value
  | query request next here _ ih => exact .query request next (weaker _ here) ih

theorem head {request : Request} {next : request.Answer → FreeQuery Programs.Spec α}
    (holds : AllQ P (.query request next)) : P request := by
  cases holds with
  | query _ _ here _ => exact here

theorem tail {request : Request} {next : request.Answer → FreeQuery Programs.Spec α}
    (holds : AllQ P (.query request next)) (answer : request.Answer) : AllQ P (next answer) := by
  cases holds with
  | query _ _ _ rest => exact rest answer

end AllQ

/-! ### Where the evaluator's queries go -/

/-- The fixed-key (fold) indices of one (lane, chunk). -/
def IndexAt (lane : Lane) (chunk : Fin chunkCount) : FixedIndex → Prop
  | .hot lane' chunk' _ _ _ => lane' = lane ∧ chunk' = chunk
  | .gadget _ _ _ _ => False

/-- The hash inputs of the cells of one (lane, chunk). -/
def CellAt (lane : Lane) (chunk : Fin chunkCount) (input : BaseField) : Prop :=
  ∃ (cell : Cell) (label : Block), cell.1.lane = lane ∧ cell.1.chunk = chunk ∧
    cellInput cell label = input

/-- A forward fixed-key query at an index in `S`. -/
def FixedAt (S : FixedIndex → Prop) : Request → Prop
  | .fixedForward index _ => S index
  | .fixedInverse _ _ => False
  | .encForward _ _ => False
  | .encInverse _ _ => False
  | .hash _ => False

/-- A hash query at an input in `S`. -/
def HashIn (S : BaseField → Prop) : Request → Prop
  | .fixedForward _ _ => False
  | .fixedInverse _ _ => False
  | .encForward _ _ => False
  | .encInverse _ _ => False
  | .hash input => S input

/-- A forward EncPRF query. -/
def EncAt : Request → Prop
  | .encForward _ _ => True
  | _ => False

/-- A query of one (lane, chunk): a forward fold query or a hash query at one of its cells. -/
def LaneAt (lane : Lane) (chunk : Fin chunkCount) (request : Request) : Prop :=
  FixedAt (IndexAt lane chunk) request ∨ HashIn (CellAt lane chunk) request

theorem hotIndexNat_indexAt (lane : Lane) (chunk : Fin chunkCount) (fold entry : Nat)
    (half : Bool) : IndexAt lane chunk (hotIndexNat lane chunk fold entry half) :=
  ⟨rfl, rfl⟩

/-- A switch's hash inputs are its cells' inputs. -/
theorem scaleInput_cellAt (lane : Lane) (chunk : Fin chunkCount)
    (switch : Fin (2 ^ chunkWidth chunk)) (limb : Fin (limbCount lane)) (label : Block) :
    CellAt lane chunk (scaleInput lane chunk switch.val limb.val label) :=
  ⟨⟨⟨lane, chunk, switch⟩, limb⟩, label, rfl, rfl, rfl⟩

section Programs

variable (lane : Lane) (chunk : Fin chunkCount)

theorem hashM_allQ (index : FixedIndex) (label : Block) (inside : IndexAt lane chunk index) :
    AllQ (FixedAt (IndexAt lane chunk)) (Programs.hashM index label) :=
  AllQ.bind (.query (.fixedForward index label) _ inside fun _ => .pure _) fun _ => .pure _

theorem foldMaskM_allQ (step entry : Nat) (label : Block) :
    AllQ (FixedAt (IndexAt lane chunk)) (Programs.foldMaskM lane chunk step entry label) :=
  (hashM_allQ lane chunk _ _ (hotIndexNat_indexAt _ _ _ _ _)).bind fun _ =>
    (hashM_allQ lane chunk _ _ (hotIndexNat_indexAt _ _ _ _ _)).bind fun _ => .pure _

theorem switchMaskM_allQ (switch : Nat) (label : Block) :
    AllQ (HashIn fun input => ∃ limb : Fin (limbCount lane),
        input = scaleInput lane chunk switch limb.val label)
      (Programs.switchMaskM lane chunk switch label) :=
  (AllQ.vector fun limb => .query (.hash _) _ ⟨limb, rfl⟩ fun _ => .pure _).bind fun _ => .pure _

theorem evalStepM_allQ (step : Nat) (bitLabel join : Block) (active : Fin (2 ^ step))
    (parent : Fin (2 ^ step) → Block) :
    AllQ (FixedAt (IndexAt lane chunk))
      (Programs.evalStepM lane chunk step bitLabel join active parent) :=
  (AllQ.vector fun _ => AllQ.ite (.pure _) (foldMaskM_allQ lane chunk _ _ _)).bind
    fun _ => .pure _

theorem evalFoldM_allQ (value : Nat) (bitLabel join : Nat → Block) :
    ∀ steps, AllQ (FixedAt (IndexAt lane chunk))
      (Programs.evalFoldM lane chunk value bitLabel join steps)
  | 0 => .pure _
  | steps + 1 => (evalFoldM_allQ value bitLabel join steps).bind fun _ =>
      (evalStepM_allQ lane chunk _ _ _ _ _).bind fun _ => .pure _

theorem evalMasksM_allQ (hot : HotLabels (chunkWidth chunk)) (alpha : Fin (2 ^ chunkWidth chunk)) :
    AllQ (HashIn (CellAt lane chunk))
      (Programs.evalMasksM lane chunk (chunkWidth chunk) hot alpha) :=
  (AllQ.vector fun switch => AllQ.ite (.pure _) ((switchMaskM_allQ lane chunk _ _).mono
    fun request inside => by
      cases request with
      | hash input =>
          obtain ⟨limb, rfl⟩ := inside
          exact scaleInput_cellAt lane chunk switch limb _
      | _ => exact inside.elim)).bind fun _ => .pure _

theorem evalChunkM_allQ (joins : Vector Block foldStepCount)
    (scale : Fin chunkCount → Fin (laneCount lane) → BaseField) (bits : BitVec coordinateBitCount)
    (labels : Fin coordinateBitCount → Block) (c : Fin chunkCount) :
    AllQ (LaneAt lane c) (Programs.evalChunkM lane joins scale bits labels c) :=
  ((evalFoldM_allQ lane c _ _ _ _).mono fun _ inside => Or.inl inside).bind fun _ =>
    ((evalMasksM_allQ lane c _ _).mono fun _ inside => Or.inr inside).bind fun _ => .pure _

end Programs

theorem padM_allQ (keys : WhiteningKeys) (coordinate : EncPRF.Coordinate)
    (index : Fin coordinateBitCount) (bit : Bool) : AllQ EncAt (Programs.padM keys coordinate index bit) :=
  AllQ.bind (.query (.encForward _ _) _ trivial fun _ => .pure _) fun _ => .pure _

theorem whitePadsM_allQ (keys : WhiteningKeys) : AllQ EncAt (whitePadsM keys) :=
  (AllQ.vector fun _ => padM_allQ _ _ _ _).bind fun _ =>
    (AllQ.vector fun _ => padM_allQ _ _ _ _).bind fun _ => .pure _

end Kriterion.ArgoMAC.Phase3.Lazy
