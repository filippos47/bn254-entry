/-
Phase 3, P4 (lazy oracle): the ideal-side lazy refill `I^U → I` (`MaskSwapBound.idealPerMask`, at
`idealRefillError = 0`) and the programming-failure (abort) bound `H → I^U`
(`keyAveragedFailBound`, at `abortQueryCharge q₁ = 1/(2^128 − q₁)`).
-/

import Proof.Privacy.Phase3.Lazy.Refill
import Proof.Privacy.Phase3.Lazy.EagerLazy
import Proof.Privacy.Phase3.Lazy.StepBound
import Proof.Privacy.Phase3.Lazy.RunBound
import Proof.Privacy.Phase3.Lazy.GameBound
import Proof.Privacy.Phase3.Lazy.StageOne
import Proof.Privacy.Phase3.Lazy.IdealPerMask
import Proof.Privacy.Phase3.Lazy.FoldEntropy
import Proof.Privacy.Phase3.Lazy.AbortReduction
import Proof.Privacy.Phase3.Lazy.AbortPerQuery
import Proof.Privacy.Phase3.Lazy.Designated
import Proof.Privacy.Phase3.Lazy.Frame
import Proof.Privacy.Phase3.Lazy.FailEvents
import Proof.Privacy.Phase3.Lazy.RunBind
import Proof.Privacy.Phase3.Lazy.Program
import Proof.Privacy.Phase3.Lazy.RunFrame
import Proof.Privacy.Phase3.Lazy.DetRun
import Proof.Privacy.Phase3.Lazy.ChunkZero
import Proof.Privacy.Phase3.Lazy.Masks
import Proof.Privacy.Phase3.Lazy.Decompose
import Proof.Privacy.Phase3.Lazy.FailHelpers
import Proof.Privacy.Phase3.Lazy.FailPoint
import Proof.Privacy.Phase3.Lazy.PointBound
import Proof.Privacy.Phase3.Lazy.FailCurve
import Proof.Privacy.Phase3.Lazy.KeyAverage
import Proof.Privacy.Phase3.Lazy.FailAssembly
