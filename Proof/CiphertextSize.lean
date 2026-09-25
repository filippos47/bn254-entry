/-
This file states the Plan B ciphertext size.

`Public` carries no `Option` tag, so every inhabitant encodes to the same length and the
obligation `Solution.ciphertextSize` -- `(encoding.encode (garble …).1).length = ciphertextBytes`
-- reduces to `Wire.encoding_length` alone. The plan source is
`2026-09-17-planB.md`, sections D.5 and Tasks 11, 12 and 19.

Layout tactic constraint: `Wire.chunkWord` is built on `Encoding.natural 20384`, so any defeq
check that reaches `List.length` of a concrete chunk word makes the kernel unfold a
20,384-fold structural recursion and abort. Every size fact below therefore goes through the
`SizedBy` lemmas of `Construction/PGS/Encoding.lean`; nothing here normalizes an encoding.
-/

import Construction.Garbling
import Construction.PGS.Encoding

namespace Kriterion.ArgoMAC.PlanB.Wire

open BN254



/-- Every Plan B public value has the declared ciphertext size. -/
theorem ciphertextSize (value : Public) :
    (encoding.encode value).length = 1082820 :=
  garble_length value

/-- The construction-facing corollary: every garbling of every tape is `1082820` bytes, because
every inhabitant of `Public` is. -/
theorem garbledCircuit_length [FieldCertificate] [GroupCertificate]
    (parameter : Nat) (scalar : NonZeroScalar) (randomness : Garbling.Randomness) :
    (encoding.encode
      ((Garbling.garbledCircuit construction).garble parameter scalar randomness).1).length =
      1082820 :=
  ciphertextSize _

/-- The constant the Plan B `Solution.ciphertextBytes` field carries. -/
theorem ciphertextBytesConstant_eq : ciphertextBytesConstant = 1082820 := rfl

end Kriterion.ArgoMAC.PlanB.Wire
