import NNH_Run6Physical
import NNH_Run6Installed
set_option autoImplicit false
noncomputable section
namespace AspisR1.NNH_Run6Top
open Aeneas Aeneas.Std Result S2Trust S2W_D189Entry S2W_D189Wrappers
open RSL RSL.TAS RSL.TASB NNH_Libraries NNH_Run6Host
open NNH_Run6Installed
variable {W Tx : Type}
/-- CONDITIONAL only. Exactly A1, A2 and Split.rest remain explicit obligations.
No row credit, condition-(4) verdict or final headline is asserted. -/
theorem deployed_splitB_conditional
 (L0 : Library W (Nat → Record)) (borrow : S2TrustedSdkBorrow L0)
 (copy : Heap (Nat → Record) → Nat → Payload → S2W_TrustedStd.Outcome (Nat → Record))
 (std : S2W_TrustedStd.TrustedStd copy)
 (allocation217 : Bytes → Env → Bool) (allocation234 : TX2_234.Args → Env → Nat → Bool)
 (ch : NMX_R4_Authentication.Choices) (alloc1 alloc2 : NMV_ConcreteWindows.Allocation)
 (a1 : NND_A1 (S (Tx := Tx) L0 copy std) VL P C)
 (a2 : NND_A2 (S (Tx := Tx) L0 copy std) L D V0)
 (rest : RestLaw (Tx := Tx) L0 copy std)
 (fx : NNH_Run5bCtx.Fixed) (w : NNH_Run5bCtx.World W Tx)
 (H : AspisV8R19.DuplexFrames.Bytes → AspisV8R19.SourceDuplexStep.State)
 (queries : (X (Tx := Tx) L0 copy std).QueriesF fx)
 (run : Runs (S (Tx := Tx) L0 copy std) (implementation allocation217 allocation234 ch alloc1 alloc2)
  (ctxB (X (Tx := Tx) L0 copy std) fx w H)) :
 let c := ctxB (X (Tx := Tx) L0 copy std) fx w H
 (S (Tx := Tx) L0 copy std).Bound c ((S (Tx := Tx) L0 copy std).model1 c) ((S (Tx := Tx) L0 copy std).model2 c) ∧
 NNH_Run5bSplit.rest L0 copy c ((S (Tx := Tx) L0 copy std).model1 c) ((S (Tx := Tx) L0 copy std).model2 c) ∧
 ((NNH_Run5bHeadlineB.headlineB L0 borrow copy std).OutcomeRec c
  ((S (Tx := Tx) L0 copy std).model1 c) ((S (Tx := Tx) L0 copy std).model2 c) ∨ (X (Tx := Tx) L0 copy std).ERec fx H) := by
 exact NNH_Run6Physical.deployed_splitB_conditional L0 borrow copy std
  (implementation allocation217 allocation234 ch alloc1 alloc2)
  allocation217 allocation234 ch alloc1 alloc2 a1 a2 rest fx w H queries run

#print axioms deployed_splitB_conditional
end AspisR1.NNH_Run6Top
end
