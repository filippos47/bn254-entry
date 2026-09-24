/-
**Task 31l — the EncPRF / bridge-key slots, enumerated.**

`ErrorBudget.t4Error` is `1024 · reductionResidue / 2 ^ 384`, and
`Stage2Assembly.encSlots_advantage_le_t4Error` spends it at a family indexed by `Fin 1024`.
Until now the `1024` was a bare count: `Construction/ArgoMAC/EncPRF.lean` gives the pads
(`evenMansourPad`, `whitenPad`) and their self-inverse laws, but no indexed enumeration of the
slots those pads are drawn at, so nothing downstream could say *which* `1024` draws `T4` pays
for.

This module supplies the enumeration, without touching `Construction/`.

### What the slots are

Every pad the EncPRF link ever computes is `EncPRF.evenMansourPad oracle keys counter` at some
`counter : EncPRF.Counter` — the whitening pad `EncPRF.whitenPad` is the same function at
`bit := false` (`Construction/ArgoMAC/EncPRF.lean`). `EncPRF.Counter` is a coordinate, a bit
position and a bit, so there are

```
2 · coordinateBitCount · 2  =  2 · 254 · 2  =  1016
```

of them: `encSlotCount` below, with `encSlotCount_le_1024` the inequality that lets `t4Error`
cover them. The count is *under* the budgeted `1024`, so nothing is weakened; `t4Error` is
quoted, never redefined.

### Rule O and Rule N

No `Fintype` instance is built by enumeration and no `Fintype.elems` is ever whnf'd:
`Fintype EncPRF.Counter` is transported along `counterEquiv`, an equivalence whose two round
trips are `rfl` by structure eta, and the cardinality is `Fintype.card_prod` plus
`Fintype.card_fin` / `Fintype.card_bool`. `encSlot` is `Fintype.equivFinOfCardEq` on that
cardinality — a bijection given by its existence proof, never evaluated. The only numerals are
`1016`, `1024` and
`254`; nothing is evaluated by `decide` or `#eval`.
-/

import Construction.ArgoMAC.EncPRF
import Mathlib.Data.Fintype.Prod
import Mathlib.Logic.Equiv.Basic

namespace Kriterion.ArgoMAC.PlanB

open BN254 Cryptography

/-! ### `EncPRF.Counter` as a product -/

/-- **An EncPRF slot is a coordinate, a bit position and a bit.** Both round trips are `rfl`:
`EncPRF.Counter` is a structure and structure eta closes them. -/
def counterEquiv :
    EncPRF.Counter ≃ EncPRF.Coordinate × Fin coordinateBitCount × Bool where
  toFun counter := (counter.coordinate, counter.index, counter.bit)
  invFun triple := ⟨triple.1, triple.2.1, triple.2.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

instance : Fintype EncPRF.Counter :=
  Fintype.ofEquiv (EncPRF.Coordinate × Fin coordinateBitCount × Bool) counterEquiv.symm

/-- There are two EncPRF coordinates. -/
theorem card_encCoordinate : Fintype.card EncPRF.Coordinate = 2 := rfl

/-- **The number of EncPRF / bridge-key slots**: one pad per coordinate, bit position and bit. -/
def encSlotCount : Nat := 1016

/-- The slot count is what the product says it is. -/
theorem card_counter : Fintype.card EncPRF.Counter = encSlotCount := by
  rw [Fintype.card_congr counterEquiv, Fintype.card_prod, Fintype.card_prod, card_encCoordinate,
    Fintype.card_fin, Fintype.card_bool, coordinateBitCount, encSlotCount]

/-- **The slots fit inside `T4`'s allowance.** `t4Error` budgets `1024` Rule S draws; the
construction makes `1016`. The term is not weakened — it is quoted, and left with slack. -/
theorem encSlotCount_le_1024 : encSlotCount ≤ 1024 := by
  rw [encSlotCount]
  norm_num

/-! ### The enumeration -/

/-- The enumeration of the EncPRF / bridge-key slots, as an equivalence. -/
noncomputable def encSlotEquiv : Fin encSlotCount ≃ EncPRF.Counter :=
  (Fintype.equivFinOfCardEq card_counter).symm

/-- **Slot number `index`.** -/
noncomputable def encSlot (index : Fin encSlotCount) : EncPRF.Counter := encSlotEquiv index

/-- The slot number of a counter. -/
noncomputable def encSlotIndex (counter : EncPRF.Counter) : Fin encSlotCount :=
  encSlotEquiv.symm counter

/-- **Distinct slot numbers are distinct slots.** -/
theorem encSlot_injective : Function.Injective encSlot := encSlotEquiv.injective

/-- **Every slot the construction uses is enumerated.** -/
theorem encSlot_surjective : Function.Surjective encSlot := encSlotEquiv.surjective

@[simp] theorem encSlot_encSlotIndex (counter : EncPRF.Counter) :
    encSlot (encSlotIndex counter) = counter := encSlotEquiv.apply_symm_apply counter

@[simp] theorem encSlotIndex_encSlot (index : Fin encSlotCount) :
    encSlotIndex (encSlot index) = index := encSlotEquiv.symm_apply_apply index

/-! ### Every EncPRF pad is one of the slots

This is the statement the `T4` step needs: the family the construction draws is indexed by
`Fin encSlotCount`, and *every* pad the link computes — the bit-dependent one of `transformAt`
and the correlation-preserving one of `whitenAt` — is read off that family. -/

/-- **The slot family**: the `1016` Even–Mansour pads, indexed. -/
noncomputable def encPadFamily (oracle : PermutationOracle EncPRF.PermutationIndex Block)
    (keys : WhiteningKeys) (index : Fin encSlotCount) : Block :=
  EncPRF.evenMansourPad oracle keys (encSlot index)

/-- Every Even–Mansour pad is one of the enumerated slots. -/
theorem evenMansourPad_eq_encPadFamily (oracle : PermutationOracle EncPRF.PermutationIndex Block)
    (keys : WhiteningKeys) (counter : EncPRF.Counter) :
    EncPRF.evenMansourPad oracle keys counter
      = encPadFamily oracle keys (encSlotIndex counter) := by
  rw [encPadFamily, encSlot_encSlotIndex]

/-- The whitening pad of a position is the slot at `bit := false`. -/
theorem whitenPad_eq_encPadFamily (oracle : PermutationOracle EncPRF.PermutationIndex Block)
    (keys : WhiteningKeys) (coordinate : EncPRF.Coordinate)
    (index : Fin coordinateBitCount) :
    EncPRF.whitenPad oracle keys coordinate index
      = encPadFamily oracle keys (encSlotIndex ⟨coordinate, index, false⟩) :=
  evenMansourPad_eq_encPadFamily oracle keys _

/-- **`transformAt` reads the slot family.** -/
theorem transformAt_eq_encPadFamily (oracle : PermutationOracle EncPRF.PermutationIndex Block)
    (keys : WhiteningKeys) (counter : EncPRF.Counter) (label : Block) :
    EncPRF.transformAt oracle keys counter label
      = encrypt (encPadFamily oracle keys (encSlotIndex counter)) label := by
  rw [EncPRF.transformAt, evenMansourPad_eq_encPadFamily]

/-- **`whitenAt` reads the slot family.** -/
theorem whitenAt_eq_encPadFamily (oracle : PermutationOracle EncPRF.PermutationIndex Block)
    (keys : WhiteningKeys) (coordinate : EncPRF.Coordinate) (index : Fin coordinateBitCount)
    (label : Block) :
    EncPRF.whitenAt oracle keys coordinate index label
      = encrypt (encPadFamily oracle keys (encSlotIndex ⟨coordinate, index, false⟩)) label := by
  rw [EncPRF.whitenAt, whitenPad_eq_encPadFamily]

/-- **The whitening keys are the bridge key's hash.** Both slots of a `WhiteningKeys` come from
one `EncPRF.HashOracle` query at the bridge key's hash input `bridgeInput value`, which is what
makes the `1016` pads a family of *bridge-key* slots rather than independent draws. -/
theorem whiteningKeys_apply (oracle : EncPRF.HashOracle) (value : BaseField) :
    EncPRF.whiteningKeys oracle value
      = { first := (oracle (bridgeInput value)).1, second := (oracle (bridgeInput value)).2 } :=
  rfl

end Kriterion.ArgoMAC.PlanB
