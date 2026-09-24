/-
This file defines the label pair of one input bit.

Plan B deletes the 254-row bit-adaptor table: the affine encodings it used to deliver are now
delivered by the projectivized garbling scheme of `Construction/PGS/*`. What survives is the
Lamport label layer -- one label pair per input bit, and the selection of one of them -- which
`Input.lean`, `EncPRF.lean` and the Lamport compatibility bridge all read.
The plan source is `2026-09-17-planB.md`, section D.4.
-/

import BN254
import Batteries.Data.Vector.Lemmas
import Cryptography.Primitives

namespace Kriterion.ArgoMAC

/-- The number of bits of one affine coordinate. -/
abbrev coordinateBitCount : Nat := 254

namespace BitAdaptor

open BN254 Cryptography

/-- A bit MAC key stores the labels for zero and one. -/
structure Key where
  /-- The label of the bit value `false`. -/
  falseLabel : Block
  /-- The label of the bit value `true`. -/
  trueLabel : Block
deriving DecidableEq

/-- The label the evaluator holds for one bit value. -/
def encode (key : Key) (value : Bool) : Block :=
  if value then key.trueLabel else key.falseLabel

end Kriterion.ArgoMAC.BitAdaptor
