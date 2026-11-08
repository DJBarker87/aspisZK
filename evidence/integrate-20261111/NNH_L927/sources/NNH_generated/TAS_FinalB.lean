import NNH_Run6Top
import NNH_Run6Charge
set_option autoImplicit false
noncomputable section
namespace AspisR1.TAS_FinalB
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
 exact NNH_Run6Top.deployed_splitB_conditional L0 borrow copy std
  allocation217 allocation234 ch alloc1 alloc2 a1 a2 rest fx w H queries run

#print axioms deployed_splitB_conditional
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw
open FS FS2
/-- CONDITIONAL outer-envelope certificate. The SAME finite recorder event
bounds every actual failure pointwise and has the single adopted charge.
No expectation on an arbitrary World-dependent indicator is invented. -/
theorem deployed_charge_conditional
 (L0 : Library W (Nat → Record)) (borrow : S2TrustedSdkBorrow L0)
 (copy : Heap (Nat → Record) → Nat → Payload → S2W_TrustedStd.Outcome (Nat → Record))
 (std : S2W_TrustedStd.TrustedStd copy)
 (allocation217 : RSL.Bytes → Env → Bool) (allocation234 : TX2_234.Args → Env → Nat → Bool)
 (ch : NMX_R4_Authentication.Choices) (alloc1 alloc2 : NMV_ConcreteWindows.Allocation)
 (a1 : NND_A1 (S (Tx := Tx) L0 copy std) VL P C)
 (a2 : NND_A2 (S (Tx := Tx) L0 copy std) L D V0)
 (rest : RestLaw (Tx := Tx) L0 copy std)
 (fx : NNH_Run5bCtx.Fixed) (anchor : AspisV8R19.DuplexFrames.Bytes → AspisV8R19.SourceDuplexStep.State)
 (queries : (X (Tx := Tx) L0 copy std).QueriesF fx)
 (wOf : (AspisV8R19.DuplexFrames.Bytes → AspisV8R19.SourceDuplexStep.State) → NNH_Run5bCtx.World W Tx) :
 (∀ H, max (0:Rat) (ind (Runs (S (Tx := Tx) L0 copy std) (implementation allocation217 allocation234 ch alloc1 alloc2)
  (ctxB (X (Tx := Tx) L0 copy std) fx (wOf H) H) ∧
 ¬ (NNH_Run5bHeadlineB.headlineB L0 borrow copy std).OutcomeRec
  (ctxB (X (Tx := Tx) L0 copy std) fx (wOf H) H)
  ((S (Tx := Tx) L0 copy std).model1 (ctxB (X (Tx := Tx) L0 copy std) fx (wOf H) H))
  ((S (Tx := Tx) L0 copy std).model2 (ctxB (X (Tx := Tx) L0 copy std) fx (wOf H) H)))) ≤ ind (BinRawByteCollisionTargets.event SelectedTranscriptParams.params.iv (fx.Q0+fx.Q1+2965)
   (eval H (NNH_Run5bRecorderFixed.fixedProgram copy fx anchor)))) ∧
 lazyMean (NNH_Run5bRecorderFixed.fixedProgram copy fx anchor) emptyTable
  (fun v => AspisV8R19.CausalFirstHitUnionBound.indicator
   (BinRawByteCollisionTargets.event SelectedTranscriptParams.params.iv (fx.Q0+fx.Q1+2965) v))
 ≤ F3T_Numeric.total (fx.Q0+fx.Q1) ∧
 (∀ H, let c := ctxB (X (Tx := Tx) L0 copy std) fx (wOf H) H
  F3T_RuntimeBound.failureModel (NNH_Run5bHost.runtime L0 copy c
   ((S (Tx := Tx) L0 copy std).model1 c) ((S (Tx := Tx) L0 copy std).model2 c)) ≤
  F3T_Numeric.total (fx.Q0+fx.Q1)) := by
 exact NNH_Run6Charge.deployed_charge_conditional L0 borrow copy std
  allocation217 allocation234 ch alloc1 alloc2 a1 a2 rest fx anchor queries wOf

#print axioms deployed_charge_conditional
end AspisR1.TAS_FinalB
end
