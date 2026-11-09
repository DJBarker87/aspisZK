import NNH_Run6Top
import NNH_Run6Charge
import NNH8_Top
import NOQ_FinalCombined
import NOF_A2FieldCorrected
set_option autoImplicit false
noncomputable section
namespace AspisR1.TAS_FinalB
open Aeneas Aeneas.Std Result S2Trust S2W_D189Entry S2W_D189Wrappers
open RSL RSL.TAS RSL.TASB NNH_Libraries NNH_Run6Host
open NNH_Run6Installed
variable {W Tx : Type}
/-! Run 6 (retained verbatim below, uncredited): two CONDITIONAL theorems at the old
host NNH_Run5bHost.S_host, superseded by the run-7 unconditional theorems at the
corrected host further down. -/
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

/-! Run 7 (G0 FINAL): the two top theorems at the corrected host
S := AspisR1.NOC_Run5bHost.S_host L0 copy std (NOC_HostSeed.m0: current op1 installed),
with EVERY interface field a delivered closed term:
 a1 := AspisR1.NOQ_FinalCombined.field, a2 := AspisR1.NOF_A2FieldCorrected.field,
 sp.rest := AspisR1.NNH8_Rest.assemble, nmfB := AspisR1.NNH8_NMF.nmfB,
 alloc1 := AspisR1.NNG_Candidate344.allocation (statement data, finding NNH-G0-F3).
No field is a binder. The adversary fx.a, the world w, the oracle H, the TX2 allocation
streams, ch, alloc2 and the trust inputs (borrow, std) stay universally quantified. -/
namespace AspisR1.TAS_FinalB
open Aeneas Aeneas.Std Result S2Trust S2W_D189Entry S2W_D189Wrappers
open RSL RSL.TAS RSL.TASB NNH_Libraries
open NNH_Run6Installed
variable {W Tx : Type}

theorem deployed_splitB
 (L0 : Library W (Nat → Record)) (borrow : S2TrustedSdkBorrow L0)
 (copy : Heap (Nat → Record) → Nat → Payload → S2W_TrustedStd.Outcome (Nat → Record))
 (std : S2W_TrustedStd.TrustedStd copy)
 (allocation217 : Bytes → Env → Bool) (allocation234 : TX2_234.Args → Env → Nat → Bool)
 (ch : NMX_R4_Authentication.Choices) (alloc2 : NMV_ConcreteWindows.Allocation)
 (fx : NOC_Run5bCtx.Fixed) (w : NOC_Run5bCtx.World W Tx)
 (H : AspisV8R19.DuplexFrames.Bytes → AspisV8R19.SourceDuplexStep.State)
 (queries : (NNH8_Exec.exec (Tx := Tx) L0 copy std).QueriesF fx)
 (run : Runs (NOC_Run5bHost.S_host (Tx := Tx) L0 copy std)
  (implementation allocation217 allocation234 ch NNG_Candidate344.allocation alloc2)
  (ctxB (NNH8_Exec.exec (Tx := Tx) L0 copy std) fx w H)) :
 let c := ctxB (NNH8_Exec.exec (Tx := Tx) L0 copy std) fx w H
 (NOC_Run5bHost.S_host (Tx := Tx) L0 copy std).Bound c
  ((NOC_Run5bHost.S_host (Tx := Tx) L0 copy std).model1 c) ((NOC_Run5bHost.S_host (Tx := Tx) L0 copy std).model2 c) ∧
 NNH8_Split.rest L0 copy c ((NOC_Run5bHost.S_host (Tx := Tx) L0 copy std).model1 c)
  ((NOC_Run5bHost.S_host (Tx := Tx) L0 copy std).model2 c) ∧
 ((NNH8_HeadlineB.headlineB L0 borrow copy std).OutcomeRec c
  ((NOC_Run5bHost.S_host (Tx := Tx) L0 copy std).model1 c) ((NOC_Run5bHost.S_host (Tx := Tx) L0 copy std).model2 c) ∨
  (NNH8_Exec.exec (Tx := Tx) L0 copy std).ERec fx H) := by
 exact NNH8_Top.deployed_splitB_of L0 borrow copy std
  allocation217 allocation234 ch NNG_Candidate344.allocation alloc2
  (NOQ_FinalCombined.field (W := W) (Tx := Tx) L0 copy std)
  (NOF_A2FieldCorrected.field (W := W) (Tx := Tx) L0 copy std)
  (NNH8_Rest.assemble (W := W) (Tx := Tx) L0 copy std) fx w H queries run

/-- Pointwise inclusion (condition (4)(i)): for EVERY oracle H and every world choice
wOf (the actual adversary fx.a, adaptive behaviour included), the actual failure event
(accepted run whose recorded Outcome fails) implies E_rec at the same H. -/
theorem fail_sub_rec
 (L0 : Library W (Nat → Record)) (borrow : S2TrustedSdkBorrow L0)
 (copy : Heap (Nat → Record) → Nat → Payload → S2W_TrustedStd.Outcome (Nat → Record))
 (std : S2W_TrustedStd.TrustedStd copy)
 (allocation217 : RSL.Bytes → Env → Bool) (allocation234 : TX2_234.Args → Env → Nat → Bool)
 (ch : NMX_R4_Authentication.Choices) (alloc2 : NMV_ConcreteWindows.Allocation)
 (fx : NOC_Run5bCtx.Fixed)
 (queries : (NNH8_Exec.exec (Tx := Tx) L0 copy std).QueriesF fx)
 (wOf : (AspisV8R19.DuplexFrames.Bytes → AspisV8R19.SourceDuplexStep.State) → NOC_Run5bCtx.World W Tx)
 (H : AspisV8R19.DuplexFrames.Bytes → AspisV8R19.SourceDuplexStep.State)
 (fail : Runs (NOC_Run5bHost.S_host (Tx := Tx) L0 copy std)
  (implementation allocation217 allocation234 ch NNG_Candidate344.allocation alloc2)
  (ctxB (NNH8_Exec.exec (Tx := Tx) L0 copy std) fx (wOf H) H) ∧
 ¬ (NNH8_HeadlineB.headlineB L0 borrow copy std).OutcomeRec
  (ctxB (NNH8_Exec.exec (Tx := Tx) L0 copy std) fx (wOf H) H)
  ((NOC_Run5bHost.S_host (Tx := Tx) L0 copy std).model1 (ctxB (NNH8_Exec.exec (Tx := Tx) L0 copy std) fx (wOf H) H))
  ((NOC_Run5bHost.S_host (Tx := Tx) L0 copy std).model2 (ctxB (NNH8_Exec.exec (Tx := Tx) L0 copy std) fx (wOf H) H))) :
 (NNH8_Exec.exec (Tx := Tx) L0 copy std).ERec fx H :=
 NNH8_Outer.inclusion L0 borrow copy std allocation217 allocation234 ch NNG_Candidate344.allocation alloc2
  (NOQ_FinalCombined.field (W := W) (Tx := Tx) L0 copy std)
  (NOF_A2FieldCorrected.field (W := W) (Tx := Tx) L0 copy std)
  (NNH8_Rest.assemble (W := W) (Tx := Tx) L0 copy std) fx queries wOf H fail

open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw
open FS FS2
/-- Condition (4)(ii): on the complete experiment (every H, the actual adversary fx.a,
any World assignment wOf), the actual failure indicator is pointwise below the SAME
fixed recorder event; that event has the single adopted accountLoss charge, which is a
summand of F3T_Numeric.total; and the failureModel <= total chain holds at every H. -/
theorem deployed_charge
 (L0 : Library W (Nat → Record)) (borrow : S2TrustedSdkBorrow L0)
 (copy : Heap (Nat → Record) → Nat → Payload → S2W_TrustedStd.Outcome (Nat → Record))
 (std : S2W_TrustedStd.TrustedStd copy)
 (allocation217 : RSL.Bytes → Env → Bool) (allocation234 : TX2_234.Args → Env → Nat → Bool)
 (ch : NMX_R4_Authentication.Choices) (alloc2 : NMV_ConcreteWindows.Allocation)
 (fx : NOC_Run5bCtx.Fixed) (anchor : AspisV8R19.DuplexFrames.Bytes → AspisV8R19.SourceDuplexStep.State)
 (queries : (NNH8_Exec.exec (Tx := Tx) L0 copy std).QueriesF fx)
 (wOf : (AspisV8R19.DuplexFrames.Bytes → AspisV8R19.SourceDuplexStep.State) → NOC_Run5bCtx.World W Tx) :
 (∀ H, max (0:Rat) (ind (Runs (NOC_Run5bHost.S_host (Tx := Tx) L0 copy std)
  (implementation allocation217 allocation234 ch NNG_Candidate344.allocation alloc2)
  (ctxB (NNH8_Exec.exec (Tx := Tx) L0 copy std) fx (wOf H) H) ∧
 ¬ (NNH8_HeadlineB.headlineB L0 borrow copy std).OutcomeRec
  (ctxB (NNH8_Exec.exec (Tx := Tx) L0 copy std) fx (wOf H) H)
  ((NOC_Run5bHost.S_host (Tx := Tx) L0 copy std).model1 (ctxB (NNH8_Exec.exec (Tx := Tx) L0 copy std) fx (wOf H) H))
  ((NOC_Run5bHost.S_host (Tx := Tx) L0 copy std).model2 (ctxB (NNH8_Exec.exec (Tx := Tx) L0 copy std) fx (wOf H) H)))) ≤
  ind (BinRawByteCollisionTargets.event SelectedTranscriptParams.params.iv (fx.Q0+fx.Q1+2965)
   (eval H (NNH8_RecorderFixed.fixedProgram copy fx anchor)))) ∧
 lazyMean (NNH8_RecorderFixed.fixedProgram copy fx anchor) emptyTable
  (fun v => AspisV8R19.CausalFirstHitUnionBound.indicator
   (BinRawByteCollisionTargets.event SelectedTranscriptParams.params.iv (fx.Q0+fx.Q1+2965) v))
 ≤ F3T_Numeric.total (fx.Q0+fx.Q1) ∧
 (∀ H, let c := ctxB (NNH8_Exec.exec (Tx := Tx) L0 copy std) fx (wOf H) H
  F3T_RuntimeBound.failureModel (NOC_Run5bHost.runtime L0 copy c
   ((NOC_Run5bHost.S_host (Tx := Tx) L0 copy std).model1 c) ((NOC_Run5bHost.S_host (Tx := Tx) L0 copy std).model2 c)) ≤
  F3T_Numeric.total (fx.Q0+fx.Q1)) := by
 exact NNH8_ChargeOf.deployed_charge_of L0 borrow copy std
  allocation217 allocation234 ch NNG_Candidate344.allocation alloc2
  (NOQ_FinalCombined.field (W := W) (Tx := Tx) L0 copy std)
  (NOF_A2FieldCorrected.field (W := W) (Tx := Tx) L0 copy std)
  (NNH8_Rest.assemble (W := W) (Tx := Tx) L0 copy std) fx anchor queries wOf

/-! Delivered-type checks (rfl) of the three model/rest fields at the corrected host. -/
example (L0 : Library W (Nat → Record))
 (copy : Heap (Nat → Record) → Nat → Payload → S2W_TrustedStd.Outcome (Nat → Record))
 (std : S2W_TrustedStd.TrustedStd copy) :
 type_of% (NOQ_FinalCombined.field (W := W) (Tx := Tx) L0 copy std) =
 NND_A1 (NOC_Run5bHost.S_host (Tx := Tx) L0 copy std) VL P C := rfl
example (L0 : Library W (Nat → Record))
 (copy : Heap (Nat → Record) → Nat → Payload → S2W_TrustedStd.Outcome (Nat → Record))
 (std : S2W_TrustedStd.TrustedStd copy) :
 type_of% (NOF_A2FieldCorrected.field (W := W) (Tx := Tx) L0 copy std) =
 NND_A2 (NOC_Run5bHost.S_host (Tx := Tx) L0 copy std) L D V0 := rfl
example (L0 : Library W (Nat → Record))
 (copy : Heap (Nat → Record) → Nat → Payload → S2W_TrustedStd.Outcome (Nat → Record))
 (std : S2W_TrustedStd.TrustedStd copy) :
 type_of% (NNH8_Rest.assemble (W := W) (Tx := Tx) L0 copy std) =
 ∀ (c : NOC_Run5bCtx.Ctx W Tx) (n1 : S2W_ExtractionBoundary.First) (n2 : S2W_ExtractionBoundary.Second),
 (NOC_Run5bHost.S_host (Tx := Tx) L0 copy std).Extraction c n1 n2 →
 (NOC_Run5bHost.S_host (Tx := Tx) L0 copy std).Accepted1 c n1 →
 (NOC_Run5bHost.S_host (Tx := Tx) L0 copy std).Game c n1 n2 →
 (NOC_Run5bHost.S_host (Tx := Tx) L0 copy std).Queries c n1 → NNH8_Split.rest L0 copy c n1 n2 := rfl
end AspisR1.TAS_FinalB

namespace AspisR1
open Aeneas Aeneas.Std Result S2Trust S2W_D189Entry S2W_D189Wrappers
open RSL RSL.TAS RSL.TASB NNH_Libraries NNH_Run6Installed
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
variable {W Tx : Type}
/-- Unconditional NNH_DeployedOuter at the corrected literal host: fail_sub_rec composed
with RSL.EVB.no_second_charge (E_rec charged once). No field argument remains. -/
theorem NNH8_DeployedOuter
 (L0 : Library W (Nat → Record)) (borrow : S2TrustedSdkBorrow L0)
 (copy : Heap (Nat → Record) → Nat → Payload → S2W_TrustedStd.Outcome (Nat → Record))
 (std : S2W_TrustedStd.TrustedStd copy)
 (allocation217 : RSL.Bytes → Env → Bool) (allocation234 : TX2_234.Args → Env → Nat → Bool)
 (ch : NMX_R4_Authentication.Choices) (alloc2 : NMV_ConcreteWindows.Allocation)
 (fx : NOC_Run5bCtx.Fixed)
 (queries : (NNH8_Exec.exec (Tx := Tx) L0 copy std).QueriesF fx)
 (r m : (AspisV8R19.DuplexFrames.Bytes → AspisV8R19.SourceDuplexStep.State) → Rat)
 (hm : ∀ H, 0 ≤ m H)
 (each : ∀ H, r H ≤ m H + ind ((NNH8_Exec.exec (Tx := Tx) L0 copy std).ERec fx H)) :
 ∀ (wOf : (AspisV8R19.DuplexFrames.Bytes → AspisV8R19.SourceDuplexStep.State) → NOC_Run5bCtx.World W Tx) (H : AspisV8R19.DuplexFrames.Bytes → AspisV8R19.SourceDuplexStep.State),
 max (r H) (ind (Runs (NOC_Run5bHost.S_host (Tx := Tx) L0 copy std)
  (implementation allocation217 allocation234 ch NNG_Candidate344.allocation alloc2)
  (ctxB (NNH8_Exec.exec (Tx := Tx) L0 copy std) fx (wOf H) H) ∧
 ¬ (NNH8_HeadlineB.headlineB L0 borrow copy std).OutcomeRec
  (ctxB (NNH8_Exec.exec (Tx := Tx) L0 copy std) fx (wOf H) H)
  ((NOC_Run5bHost.S_host (Tx := Tx) L0 copy std).model1 (ctxB (NNH8_Exec.exec (Tx := Tx) L0 copy std) fx (wOf H) H))
  ((NOC_Run5bHost.S_host (Tx := Tx) L0 copy std).model2 (ctxB (NNH8_Exec.exec (Tx := Tx) L0 copy std) fx (wOf H) H)))) ≤
 m H + ind ((NNH8_Exec.exec (Tx := Tx) L0 copy std).ERec fx H) :=
 NNH8_DeployedOuterOf L0 borrow copy std allocation217 allocation234 ch NNG_Candidate344.allocation alloc2
  (NOQ_FinalCombined.field (W := W) (Tx := Tx) L0 copy std)
  (NOF_A2FieldCorrected.field (W := W) (Tx := Tx) L0 copy std)
  (NNH8_Rest.assemble (W := W) (Tx := Tx) L0 copy std) fx queries r m hm each
end AspisR1
end
#print axioms AspisR1.TAS_FinalB.deployed_splitB_conditional
#print axioms AspisR1.TAS_FinalB.deployed_charge_conditional
#print axioms AspisR1.TAS_FinalB.deployed_splitB
#print axioms AspisR1.TAS_FinalB.fail_sub_rec
#print axioms AspisR1.TAS_FinalB.deployed_charge
#print axioms AspisR1.NNH8_DeployedOuter
