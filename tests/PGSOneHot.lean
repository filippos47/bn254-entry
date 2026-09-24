/-
This test exercises the Plan B `bin-to-hot` fold against a concrete toy permutation family.
It is not shipped: the verifier copies only `Construction*`, `Proof*` and `Submission`.

`checkAll width` asserts the free-XOR invariant `E_t = Z_t ^^^ h_t * delta` at every entry of
every chunk value, which is the statement Task 7 proves symbolically
(`Proof/Correctness/PGS/OneHot.lean`, `evalHot_garbleHot`).

Run with `lake env lean tests/PGSOneHot.lean`; every `#eval` must print `true`.
-/

import Construction.PGS.OneHot
namespace Kriterion.ArgoMAC.PlanB
open Cryptography

def addEquiv (c : Block) : Equiv Block Block where
  toFun x := x + c
  invFun x := x - c
  left_inv x := by simp
  right_inv x := by simp

def coordNat : Coord → Nat | .x => 0 | .y => 1

def laneNat : Lane → Nat | .curveX => 0 | .curveY => 1 | .pointX => 2 | .pointY => 3

def keyOf : FixedIndex → Block
  | .hot c k j r h => BitVec.ofNat 128
      (1000003 + 7919 * laneNat c + 104729 * k.val + 1299709 * j.val + 15485863 * r.val
        + 2750159 * (if h then 1 else 0))
  | .gadget d c q => BitVec.ofNat 128 (3000017 + 7919 * d.val + 104729 * coordNat c + 1299709 * q.val)

def testOracle : PermutationOracle FixedIndex Block := ⟨fun i => addEquiv (keyOf i)⟩

def delta : Block := BitVec.ofNat 128 0xdeadbeefcafebabe0123456789abcdef

def zeroLabel (width position : Nat) : Block :=
  BitVec.ofNat 128 (777 + 65537 * width + 2654435761 * position)

def bitKey (width : Nat) : Fin width → Block × Block :=
  fun position => (zeroLabel width position.val, zeroLabel width position.val ^^^ delta)

/-- For one width and one chunk value, does the evaluator's label vector equal the garbler's
masks XOR the one-hot times delta? -/
def check (width : Nat) (chunk : Fin chunkCount) (lane : Lane) (value : BitVec width) : Bool :=
  let zeros : Fin width → Block := fun p => (bitKey width p).1
  let g := garbleHot testOracle lane chunk width delta zeros
  let e := evalHot testOracle lane chunk width g.2 (selectBits (bitKey width) value) value
  (List.finRange (2 ^ width)).all fun entry =>
    e entry == g.1 entry ^^^ (if binToHot width value entry then delta else 0)

def checkAll (width : Nat) : Bool :=
  (List.finRange (2 ^ width)).all fun v =>
    check width ⟨0, by decide⟩ .curveX (BitVec.ofNat width v.val) &&
    check width ⟨18, by decide⟩ .pointY (BitVec.ofNat width v.val)

#eval checkAll 1
#eval checkAll 2
#eval checkAll 3
#eval checkAll 4
#eval checkAll 6

-- The published join count is `width - 1`.
#eval (garbleHot testOracle .pointX ⟨0, by decide⟩ 14 delta (fun p => (bitKey 14 p).1)).2.size

end Kriterion.ArgoMAC.PlanB
