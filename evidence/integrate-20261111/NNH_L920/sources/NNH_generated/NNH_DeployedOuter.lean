import NNH_Run6Top
set_option autoImplicit false
noncomputable section
namespace AspisR1.NNH_Run6Outer
open Aeneas Aeneas.Std Result S2Trust S2W_D189Entry S2W_D189Wrappers
open RSL RSL.TAS RSL.TASB NNH_Libraries NNH_Run6Host NNH_Run6Installed
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
variable {W Tx : Type}
theorem inclusion
 (L0 : Library W (Nat → Record)) (borrow : S2TrustedSdkBorrow L0)
 (copy : Heap (Nat → Record) → Nat → Payload → S2W_TrustedStd.Outcome (Nat → Record))
 (std : S2W_TrustedStd.TrustedStd copy)
 (allocation217 : RSL.Bytes → Env → Bool) (allocation234 : TX2_234.Args → Env → Nat → Bool)
 (ch : NMX_R4_Authentication.Choices) (alloc1 alloc2 : NMV_ConcreteWindows.Allocation)
 (a1 : NND_A1 (S (Tx := Tx) L0 copy std) VL P C)
 (a2 : NND_A2 (S (Tx := Tx) L0 copy std) L D V0)
 (rest : RestLaw (Tx := Tx) L0 copy std)
 (fx : NNH_Run5bCtx.Fixed)
 (queries : (X (Tx := Tx) L0 copy std).QueriesF fx)
 (wOf : (Bytes → State) → NNH_Run5bCtx.World W Tx) (H : Bytes → State)
 (fail : (Runs (S (Tx := Tx) L0 copy std) (implementation allocation217 allocation234 ch alloc1 alloc2)
  (ctxB (X (Tx := Tx) L0 copy std) fx (wOf H) H) ∧
 ¬ (NNH_Run5bHeadlineB.headlineB L0 borrow copy std).OutcomeRec
  (ctxB (X (Tx := Tx) L0 copy std) fx (wOf H) H)
  ((S (Tx := Tx) L0 copy std).model1 (ctxB (X (Tx := Tx) L0 copy std) fx (wOf H) H))
  ((S (Tx := Tx) L0 copy std).model2 (ctxB (X (Tx := Tx) L0 copy std) fx (wOf H) H)))) : (X (Tx := Tx) L0 copy std).ERec fx H := by
 rcases (NNH_Run6Top.deployed_splitB_conditional L0 borrow copy std
  allocation217 allocation234 ch alloc1 alloc2 a1 a2 rest fx (wOf H) H queries fail.1).2.2 with o | e
 · exact absurd o fail.2
 · exact e
#print axioms inclusion
end AspisR1.NNH_Run6Outer

namespace AspisR1
open Aeneas Aeneas.Std Result S2Trust S2W_D189Entry S2W_D189Wrappers
open RSL RSL.TAS RSL.TASB NNH_Libraries NNH_Run6Host NNH_Run6Installed
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
variable {W Tx : Type}
/-- CONDITIONAL physical fail_sub_rec plus EVB.no_second_charge at the literal host.
The three missing field arguments are retained visibly. -/
theorem NNH_DeployedOuter
 (L0 : Library W (Nat → Record)) (borrow : S2TrustedSdkBorrow L0)
 (copy : Heap (Nat → Record) → Nat → Payload → S2W_TrustedStd.Outcome (Nat → Record))
 (std : S2W_TrustedStd.TrustedStd copy)
 (allocation217 : RSL.Bytes → Env → Bool) (allocation234 : TX2_234.Args → Env → Nat → Bool)
 (ch : NMX_R4_Authentication.Choices) (alloc1 alloc2 : NMV_ConcreteWindows.Allocation)
 (a1 : NND_A1 (S (Tx := Tx) L0 copy std) VL P C)
 (a2 : NND_A2 (S (Tx := Tx) L0 copy std) L D V0)
 (rest : RestLaw (Tx := Tx) L0 copy std)
 (fx : NNH_Run5bCtx.Fixed)
 (queries : (X (Tx := Tx) L0 copy std).QueriesF fx)
 (r m : (Bytes → State) → Rat)
 (hm : ∀ H, 0 ≤ m H)
 (each : ∀ H, r H ≤ m H + ind ((X (Tx := Tx) L0 copy std).ERec fx H)) :
 ∀ (wOf : (Bytes → State) → NNH_Run5bCtx.World W Tx) (H : Bytes → State),
 max (r H) (ind (Runs (S (Tx := Tx) L0 copy std) (implementation allocation217 allocation234 ch alloc1 alloc2)
  (ctxB (X (Tx := Tx) L0 copy std) fx (wOf H) H) ∧
 ¬ (NNH_Run5bHeadlineB.headlineB L0 borrow copy std).OutcomeRec
  (ctxB (X (Tx := Tx) L0 copy std) fx (wOf H) H)
  ((S (Tx := Tx) L0 copy std).model1 (ctxB (X (Tx := Tx) L0 copy std) fx (wOf H) H))
  ((S (Tx := Tx) L0 copy std).model2 (ctxB (X (Tx := Tx) L0 copy std) fx (wOf H) H)))) ≤ m H + ind ((X (Tx := Tx) L0 copy std).ERec fx H) := by
 classical
 intro wOf H
 rw [ind_def,ind_def]
 have e := each H
 rw [ind_def] at e
 exact RSL.EVB.no_second_charge (r H) (m H) _ _ (hm H) e
  (fun fail => NNH_Run6Outer.inclusion L0 borrow copy std
   allocation217 allocation234 ch alloc1 alloc2 a1 a2 rest fx queries wOf H fail)
#print axioms NNH_DeployedOuter
end AspisR1
end
