/-
**Bit lists of the wire, and the protocol's byte parse.**

`lsbs width value` is the list of the low `width` bits of `value`, least significant first: what
`SimulatorProtocol.bits` produces, what the machine's emitter pushes, and what the flattened
little-endian byte encodings read as (`natural_byteBits`). `vector_encode` flattens a vector
encoding.

`publicValue_encode`: the protocol's parse of the bits of an encoding (`words 8`, then
`decode`, then the canonical re-encoding check) returns the encoded value, for every encoding of
fixed length.
-/

import Security.AdaptivePrivacy

namespace Kriterion.ArgoMAC.PlanB.SimMachine

open Kriterion.GarbledCircuit

/-- The low `width` bits of `value`, least significant first. -/
def lsbs (width value : Nat) : List Bool := List.ofFn fun index : Fin width => value.testBit index

theorem lsbs_length (width value : Nat) : (lsbs width value).length = width := by
  simp [lsbs]

theorem lsbs_zero (value : Nat) : lsbs 0 value = [] := rfl

/-- Splitting a bit run. -/
theorem lsbs_add (first second value : Nat) :
    lsbs (first + second) value = lsbs first value ++ lsbs second (value / 2 ^ first) := by
  unfold lsbs
  rw [List.ofFn_add]
  congr 1 <;> refine congrArg List.ofFn (funext fun index => ?_) <;>
    simp [Nat.testBit_div_two_pow, Nat.add_comm]

/-- The low bits depend only on the residue. -/
theorem lsbs_mod (width value : Nat) : lsbs width (value % 2 ^ width) = lsbs width value := by
  unfold lsbs
  refine congrArg List.ofFn (funext fun index => ?_)
  simp [Nat.testBit_mod_two_pow, index.isLt]

/-- The protocol's bit expansion. -/
theorem bits_eq_lsbs (width value : Nat) :
    SimulatorProtocol.bits width value = lsbs width value := by
  unfold SimulatorProtocol.bits lsbs
  rw [List.ofFn_eq_map]
  refine List.map_congr_left fun index _ => ?_
  simp only [BitVec.getLsb, BitVec.toNat_ofNat, Nat.testBit_mod_two_pow, index.isLt,
    decide_true, Bool.true_and]

/-- The byte bits of a byte list. -/
def byteBits (bytes : List (Fin 256)) : List Bool :=
  bytes.flatMap fun byte => SimulatorProtocol.bits 8 byte.val

theorem byteBits_append (first second : List (Fin 256)) :
    byteBits (first ++ second) = byteBits first ++ byteBits second := by
  simp [byteBits]

theorem byteBits_length (bytes : List (Fin 256)) : (byteBits bytes).length = 8 * bytes.length := by
  induction bytes with
  | nil => rfl
  | cons byte rest ih =>
      simp only [byteBits, List.flatMap_cons, List.length_append, bits_eq_lsbs, lsbs_length,
        List.length_cons] at ih ⊢
      omega

/-- **A little-endian natural encoding reads as its low bits.** -/
theorem natural_byteBits : ∀ (width : Nat) (value : Fin (256 ^ width)),
    byteBits ((Encoding.natural width).encode value) = lsbs (8 * width) value.val
  | 0, value => by
      have : value.val = 0 := by have := value.isLt; simpa using this
      rfl
  | width + 1, value => by
      show byteBits (⟨value.val % 256, Nat.mod_lt _ (by decide)⟩ ::
          (Encoding.natural width).encode ⟨value.val / 256, _⟩) = _
      rw [show byteBits (⟨value.val % 256, Nat.mod_lt _ (by decide)⟩ ::
          (Encoding.natural width).encode ⟨value.val / 256, by
            have := value.isLt; simp only [pow_succ] at this; omega⟩) =
          SimulatorProtocol.bits 8 (value.val % 256) ++
            byteBits ((Encoding.natural width).encode ⟨value.val / 256, by
              have := value.isLt; simp only [pow_succ] at this; omega⟩) from rfl,
        natural_byteBits width, bits_eq_lsbs, show 8 * (width + 1) = 8 + 8 * width by ring,
        lsbs_add]
      congr 1
      exact lsbs_mod 8 value.val

/-- A vector encoding is the concatenation of its entries' encodings. -/
theorem vector_encode {α : Type} (encoding : Encoding α) : ∀ (count : Nat) (values : Vector α count),
    (encoding.vector count).encode values =
      (List.ofFn fun index : Fin count => encoding.encode values[index.val]).flatten
  | 0, values => rfl
  | count + 1, values => by
      show (encoding.vector count).encode values.pop ++ encoding.encode values.back = _
      rw [vector_encode encoding count, List.ofFn_succ_last, List.flatten_concat]
      congr 1
      refine congrArg List.flatten (congrArg List.ofFn (funext fun index => ?_))
      simp

/-! ### The protocol's byte parse -/

/-- The little-endian fold of eight emitted bits recovers the byte. -/
theorem fold_bits_byte (byte : Fin 256) :
    (SimulatorProtocol.bits 8 byte.val).foldr (fun bit acc => bit.toNat + 2 * acc) 0 = byte.val := by
  have small := byte.isLt
  generalize byte.val = value at small ⊢
  interval_cases value <;> rfl

theorem drop_byteBits (bytes : List (Fin 256)) (count : Nat) :
    (byteBits bytes).drop (8 * count) = byteBits (bytes.drop count) := by
  induction bytes generalizing count with
  | nil => simp [byteBits]
  | cons byte rest ih =>
      cases count with
      | zero => simp
      | succ count =>
          simp only [byteBits, List.flatMap_cons, List.drop_succ_cons]
          rw [show 8 * (count + 1) = 8 + 8 * count by ring, ← List.drop_drop,
            List.drop_left' (by rw [bits_eq_lsbs, lsbs_length])]
          exact ih count

theorem take_byteBits (byte : Fin 256) (rest : List (Fin 256)) :
    (byteBits (byte :: rest)).take 8 = SimulatorProtocol.bits 8 byte.val := by
  simp only [byteBits, List.flatMap_cons]
  rw [List.take_left' (by rw [bits_eq_lsbs, lsbs_length])]

/-- **The byte parse of the bits of a byte list** is the byte list. -/
theorem words_byteBits (bytes : List (Fin 256)) :
    SimulatorProtocol.words 8 bytes.length (byteBits bytes) =
      some (Vector.ofFn fun index : Fin bytes.length => BitVec.ofNat 8 bytes[index.val].val) := by
  unfold SimulatorProtocol.words
  rw [if_pos (by rw [byteBits_length, Nat.mul_comm])]
  congr 1
  refine congrArg Vector.ofFn (funext fun index => ?_)
  congr 1
  rw [show index.val * 8 = 8 * index.val by ring, drop_byteBits,
    List.drop_eq_getElem_cons index.isLt, take_byteBits, fold_bits_byte]

/-- **The protocol's parse of an encoding's bits returns the encoded value.** -/
theorem publicValue_encode {Public : Type} (encoding : Encoding Public) (length : Nat)
    (value : Public) (sized : (encoding.encode value).length = length) :
    SimulatorProtocol.publicValue encoding length (byteBits (encoding.encode value)) =
      some value := by
  subst sized
  unfold SimulatorProtocol.publicValue
  rw [words_byteBits]
  have raw : ((Vector.ofFn fun index : Fin (encoding.encode value).length =>
      BitVec.ofNat 8 (encoding.encode value)[index.val].val).map BitVec.toFin).toList =
      encoding.encode value := by
    apply List.ext_getElem
    · simp
    · intro index first second
      simp only [Vector.toList_map, Vector.toList_ofFn, List.getElem_map, List.getElem_ofFn]
      apply Fin.ext
      simp [Nat.mod_eq_of_lt (encoding.encode value)[index].isLt]
  have decoded : encoding.decode (encoding.encode value) = some (value, []) := by
    have := encoding.decode_encode value []
    rwa [List.append_nil] at this
  simp only [Option.bind_eq_bind, Option.bind_some]
  rw [raw, decoded]
  simp

end Kriterion.ArgoMAC.PlanB.SimMachine
