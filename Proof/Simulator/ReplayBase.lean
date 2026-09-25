/-
**The replay's toolkit.**

* `blockWord`, `fieldWord`: how the machine's words carry blocks and field elements;
* `query_fixed`, `query_enc`, `query_hash`: `queryFromRegisters` decodes the ordinal constants the
  replay embeds (at the `planBSimulator` instances);
* `Agree.map`, `Agree.query`, `agree_rep_vector`: the tree agreements the replay is assembled
  from (a machine `rep` against an intercepted abstract `FreeQuery.vector`);
* `tree_rep_front`, `tree_rep_add`: reassociations of `rep` trees.
-/

import Proof.Simulator.Tree

namespace Kriterion.ArgoMAC.PlanB.SimMachine

open BN254 Cryptography Cryptography.BoundedMachine Blocks
open Kriterion.ArgoMAC.Phase3.Glue

noncomputable section

/-! ### Words -/

/-- A block zero-extended to a word. -/
def blockWord (block : Block) : Word := BitVec.ofNat 256 block.toNat

/-- A field element as its canonical word. -/
def fieldWord (value : BaseField) : Word := BitVec.ofNat 256 value.val

theorem blockWord_toNat (block : Block) : (blockWord block).toNat = block.toNat := by
  unfold blockWord
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (lt_trans block.isLt (by norm_num))]

theorem blockWord_block (block : Block) : BitVec.ofNat 128 (blockWord block).toNat = block := by
  rw [blockWord_toNat, BitVec.ofNat_toNat, BitVec.setWidth_eq]

theorem blockWord_xor (first second : Block) :
    blockWord first ^^^ blockWord second = blockWord (first ^^^ second) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_xor, blockWord_toNat, blockWord_toNat, blockWord_toNat, BitVec.toNat_xor]

theorem fieldWord_toNat (value : BaseField) : (fieldWord value).toNat = value.val := by
  unfold fieldWord
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (lt_trans value.val_lt (by unfold baseFieldModulus; norm_num))]

theorem fieldWord_cast (value : BaseField) : (((fieldWord value).toNat : Nat) : BaseField) = value := by
  rw [fieldWord_toNat, ZMod.natCast_zmod_val]

theorem fieldWord_injective {first second : BaseField} (same : fieldWord first = fieldWord second) :
    first = second := by
  rw [← fieldWord_cast first, ← fieldWord_cast second, same]

variable [FieldCertificate]

theorem eval_fieldAdd (first second : Word) :
    Arithmetic.fieldAdd.eval first second =
      fieldWord ((first.toNat : BaseField) + (second.toNat : BaseField)) := rfl

theorem eval_fieldSub (first second : Word) :
    Arithmetic.fieldSub.eval first second =
      fieldWord ((first.toNat : BaseField) - (second.toNat : BaseField)) := rfl

theorem eval_fieldMul (first second : Word) :
    Arithmetic.fieldMul.eval first second =
      fieldWord ((first.toNat : BaseField) * (second.toNat : BaseField)) := rfl

/-! ### The ordinal constants decode -/

/-- The fixed-index ordinals at the `planBSimulator` instance. -/
abbrev ordF0 : PlanB.FixedIndex → Nat := @ordinal PlanB.FixedIndex (Fintype.ofFinite _)

/-- The EncPRF-index ordinals at the `planBSimulator` instance. -/
abbrev ordE0 : EncPRF.PermutationIndex → Nat := @ordinal EncPRF.PermutationIndex (Fintype.ofFinite _)

omit [FieldCertificate] in
theorem card_fixed_ofFinite : @Fintype.card PlanB.FixedIndex (Fintype.ofFinite _) = 159016 :=
  calc @Fintype.card PlanB.FixedIndex (Fintype.ofFinite _) = Nat.card PlanB.FixedIndex :=
        @Fintype.card_eq_nat_card _ (Fintype.ofFinite _)
    _ = Fintype.card PlanB.FixedIndex := Fintype.card_eq_nat_card.symm
    _ = 159016 := card_fixedIndex

omit [FieldCertificate] in
theorem card_enc_ofFinite : @Fintype.card EncPRF.PermutationIndex (Fintype.ofFinite _) = 508 :=
  calc @Fintype.card EncPRF.PermutationIndex (Fintype.ofFinite _) = Nat.card EncPRF.PermutationIndex :=
        @Fintype.card_eq_nat_card _ (Fintype.ofFinite _)
    _ = Fintype.card EncIndex := Fintype.card_eq_nat_card.symm
    _ = 508 := card_encIndex

omit [FieldCertificate] in
theorem ordF0_lt (index : PlanB.FixedIndex) :
    ordF0 index < @Fintype.card PlanB.FixedIndex (Fintype.ofFinite _) :=
  (@Fintype.equivFin PlanB.FixedIndex (Fintype.ofFinite _) index).isLt

omit [FieldCertificate] in
theorem ordE0_lt (index : EncPRF.PermutationIndex) :
    ordE0 index < @Fintype.card EncPRF.PermutationIndex (Fintype.ofFinite _) :=
  (@Fintype.equivFin EncPRF.PermutationIndex (Fintype.ofFinite _) index).isLt

omit [FieldCertificate] in
theorem word_ordF0 (index : PlanB.FixedIndex) : (word (ordF0 index)).toNat = ordF0 index := by
  have bound := ordF0_lt index
  rw [card_fixed_ofFinite] at bound
  rw [word, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]

omit [FieldCertificate] in
theorem word_ordE0 (index : EncPRF.PermutationIndex) : (word (ordE0 index)).toNat = ordE0 index := by
  have bound := ordE0_lt index
  rw [card_enc_ofFinite] at bound
  rw [word, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]

omit [FieldCertificate] in
theorem equivFin_ordF0 (index : PlanB.FixedIndex) (bound : ordF0 index < _) :
    (@Fintype.equivFin PlanB.FixedIndex (Fintype.ofFinite _)).symm ⟨ordF0 index, bound⟩ = index :=
  (@Fintype.equivFin PlanB.FixedIndex (Fintype.ofFinite _)).symm_apply_apply index

omit [FieldCertificate] in
theorem equivFin_ordE0 (index : EncPRF.PermutationIndex) (bound : ordE0 index < _) :
    (@Fintype.equivFin EncPRF.PermutationIndex (Fintype.ofFinite _)).symm ⟨ordE0 index, bound⟩ =
      index :=
  (@Fintype.equivFin EncPRF.PermutationIndex (Fintype.ofFinite _)).symm_apply_apply index

omit [FieldCertificate] in
/-- **A fixed forward query decodes to its index.** -/
theorem query_fixed (index : PlanB.FixedIndex) (input : Word) :
    @queryFromRegisters PlanB.FixedIndex EncPRF.PermutationIndex (Fintype.ofFinite _)
        (Fintype.ofFinite _) 0 (word (ordF0 index)) input =
      some (.fixedForward index (BitVec.ofNat 128 input.toNat)) := by
  unfold queryFromRegisters
  simp only [word_ordF0]
  rw [dif_pos (ordF0_lt index)]
  simp only [equivFin_ordF0]
  rfl

omit [FieldCertificate] in
/-- **An EncPRF forward query decodes to its index.** -/
theorem query_enc (index : EncPRF.PermutationIndex) (input : Word) :
    @queryFromRegisters PlanB.FixedIndex EncPRF.PermutationIndex (Fintype.ofFinite _)
        (Fintype.ofFinite _) 2 (word (ordE0 index)) input =
      some (.encForward index (BitVec.ofNat 128 input.toNat)) := by
  unfold queryFromRegisters
  simp only [word_ordE0]
  rw [dif_pos (ordE0_lt index)]
  simp only [equivFin_ordE0]
  rfl

/-- **A hash query decodes to its input.** -/
theorem query_hash (index input : Word) :
    @queryFromRegisters PlanB.FixedIndex EncPRF.PermutationIndex (Fintype.ofFinite _)
        (Fintype.ofFinite _) 4 index input = some (.hash (input.toNat : BaseField)) := by
  unfold queryFromRegisters
  rfl

/-! ### Trees at the `planBSimulator` instances -/

/-- A machine block's tree at the `planBSimulator` instances. -/
abbrev rtree (program : Prog) (memory : Memory) : FreeQuery Programs.Spec (Option Memory) :=
  @Prog.tree _ PlanB.FixedIndex EncPRF.PermutationIndex (Fintype.ofFinite _) (Fintype.ofFinite _)
    program memory

theorem rtree_seq (first second : Prog) (memory : Memory) :
    rtree (.seq first second) memory = bindOpt (rtree first memory) (rtree second) := rfl

omit [FieldCertificate] in
theorem bindOpt_pure {spec : OracleSpec.{0, 0}} (memory : Memory)
    (next : Memory → FreeQuery spec (Option Memory)) :
    bindOpt (.pure (some memory)) next = next memory := rfl

omit [FieldCertificate] in
theorem bindOpt_assoc {spec : OracleSpec.{0, 0}} (tree : FreeQuery spec (Option Memory))
    (first second : Memory → FreeQuery spec (Option Memory)) :
    bindOpt (bindOpt tree first) second = bindOpt tree fun memory => bindOpt (first memory) second := by
  unfold bindOpt
  rw [TreeLaws.bind_assoc]
  congr 1
  funext result
  cases result <;> rfl

omit [FieldCertificate] in
theorem bindOpt_pure_right {spec : OracleSpec.{0, 0}} (tree : FreeQuery spec (Option Memory)) :
    bindOpt tree (fun memory => .pure (some memory)) = tree := by
  unfold bindOpt
  conv_rhs => rw [← TreeLaws.bind_pure_right tree]
  congr 1
  funext result
  cases result <;> rfl

/-- `rep` peeled at the front, on trees. -/
theorem tree_rep_front (count : Nat) (body : Nat → Prog) (memory : Memory) :
    rtree (Prog.rep (count + 1) body) memory =
      bindOpt (rtree (body 0) memory) (rtree (Prog.rep count fun index => body (index + 1))) := by
  induction count generalizing memory with
  | zero =>
      rw [Prog.rep, Prog.rep, Prog.rep]
      simp only [rtree_seq]
      show bindOpt (.pure (some memory)) _ = _
      rw [bindOpt_pure]
      exact (bindOpt_pure_right _).symm
  | succ count ih =>
      rw [Prog.rep, rtree_seq, ih, Prog.rep, bindOpt_assoc]
      rfl

/-- `rep` of a sum, on trees. -/
theorem tree_rep_add (first second : Nat) (body : Nat → Prog) (memory : Memory) :
    rtree (Prog.rep (first + second) body) memory =
      bindOpt (rtree (Prog.rep first body) memory)
        (rtree (Prog.rep second fun index => body (first + index))) := by
  induction second generalizing memory with
  | zero =>
      rw [Nat.add_zero, Prog.rep]
      exact (bindOpt_pure_right _).symm
  | succ second ih =>
      rw [← Nat.add_assoc, Prog.rep, rtree_seq, ih, Prog.rep, bindOpt_assoc]
      rfl

/-! ### Agreement toolkit -/

omit [FieldCertificate] in
/-- Map the abstract leaves. -/
theorem Agree.map {β γ : Type} {Post : β → Memory → Prop} {Post' : γ → Memory → Prop}
    (f : β → γ) (related : ∀ value memory, Post value memory → Post' (f value) memory) :
    ∀ {tree : FreeQuery Programs.Spec (Option Memory)} {tree' : FreeQuery Programs.Spec β},
      Agree Post tree tree' → Agree Post' tree (FreeQuery.bind tree' fun value => .pure (f value))
  | _, _, .leaf holds => .leaf (related _ _ holds)
  | _, _, .node request each => .node request fun answer => (each answer).map f related

/-- A query instruction against the same abstract question. -/
theorem Agree.query {β : Type} {Post : β → Memory → Prop} (kind : Fin 5)
    (index input first second : Register) (memory : Memory)
    (request : PublicQuery PlanB.FixedIndex EncPRF.PermutationIndex)
    (decode : @queryFromRegisters PlanB.FixedIndex EncPRF.PermutationIndex (Fintype.ofFinite _)
      (Fintype.ofFinite _) kind (memory.registers index) (memory.registers input) = some request)
    (rest : Memory → FreeQuery Programs.Spec (Option Memory))
    (next : request.Answer → FreeQuery Programs.Spec β)
    (each : ∀ answer, Agree Post (rest (writePair memory first second (answerWords request answer)))
      (next answer)) :
    Agree Post (SimMachine.bindOpt (rtree (.op (.query kind index input first second)) memory) rest)
      (.query request next) := by
  simp only [rtree, Prog.tree, Op.tree]
  rw [decode]
  exact .node request each

/-- **A machine `rep` against an intercepted abstract vector**, with an invariant on the
collected values, the record and the memory. -/
theorem agree_rep_vector {α : Type} (bits : BitInput)
    (body : Nat → Prog) (Inv : (count : Nat) → Vector α count × DesignatedRecord → Memory → Prop) :
    ∀ (count : Nat) (program : Fin count → FreeQuery Programs.Spec α),
      (∀ (index : Fin count) (values : Vector α index.val) (record : DesignatedRecord)
          (memory : Memory),
        Inv index.val (values, record) memory →
          Agree (fun (result : α × DesignatedRecord) after =>
              Inv (index.val + 1) (values.push result.1, result.2) after)
            (rtree (body index.val) memory) (interceptT bits (program index) record)) →
      ∀ (record : DesignatedRecord) (memory : Memory), Inv 0 (#v[], record) memory →
        Agree (Inv count) (rtree (Prog.rep count body) memory)
          (interceptT bits (FreeQuery.vector count program) record)
  | 0, _, _, record, memory, start => by
      rw [Prog.rep]
      exact .leaf start
  | count + 1, program, step, record, memory, start => by
      rw [Prog.rep, rtree_seq]
      simp only [FreeQuery.vector, TreeLaws.monad_bind, TreeLaws.monad_pure, interceptT_bind]
      refine Agree.bindOpt (fun collected middle holds => ?_)
        (agree_rep_vector bits body Inv count (fun index => program index.castSucc)
          (fun index values record memory holds => step index.castSucc values record memory holds)
          record memory start)
      have last : Agree (fun (result : α × DesignatedRecord) after =>
            Inv (count + 1) (collected.1.push result.1, result.2) after)
          (rtree (body count) middle) (interceptT bits (program (Fin.last count)) collected.2) :=
        step (Fin.last count) collected.1 collected.2 middle holds
      have mapped : Agree (Inv (count + 1)) (rtree (body count) middle)
          (FreeQuery.bind (interceptT bits (program (Fin.last count)) collected.2)
            fun result => .pure (collected.1.push result.1, result.2)) :=
        Agree.map (Post := fun result after =>
            Inv (count + 1) (collected.1.push result.1, result.2) after)
          (fun result : α × DesignatedRecord => (collected.1.push result.1, result.2))
          (fun _ _ holds => holds) last
      exact mapped

end

end Kriterion.ArgoMAC.PlanB.SimMachine
