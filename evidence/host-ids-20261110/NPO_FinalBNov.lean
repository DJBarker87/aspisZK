import NPO_CloneNov
set_option autoImplicit false
noncomputable section
namespace NPO_ProgramNov
open Aeneas Aeneas.Std
/-- CPH_Program.verifier with the id replaced by the Nov deployment's verifier id. -/
abbrev verifier : AspisR1.S2W_ExtractionBoundary.Program := NPO_DeployedIds.verifierNov
end NPO_ProgramNov
namespace NPO_InstancesNov
/-- LIB_Instances.D with the Pool/registry ids replaced (the kernel-checked clone). -/
abbrev D : RSL.DeployedIds := NPO_Nov.LIB_Instances.D
theorem D_eq : D = NPO_DeployedIds.DNov := rfl
end NPO_InstancesNov
namespace AspisR1.NPO_Run5bHostNov
open Aeneas Aeneas.Std Result S2Trust S2W_D189Entry S2W_D189Wrappers
open RSL RSL.TAS RSL.TASB NNH_Libraries
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep AspisV8R19.MemoizedProgramLaw
variable {W Tx : Type}
/-- NOC_Run5bHost.S_host built by the same construction at the Nov ids. -/
abbrev S_host := @NPO_Nov.AspisR1.NOC_Run5bHost.S_host
theorem type_same : type_of% @S_host = type_of% @AspisR1.NOC_Run5bHost.S_host := rfl
theorem ctx_same (L : Library W (Nat → Record))
 (copy : Heap (Nat → Record) → Nat → Payload → S2W_TrustedStd.Outcome (Nat → Record))
 (std : S2W_TrustedStd.TrustedStd copy) :
 (S_host (Tx := Tx) L copy std).Ctx = (AspisR1.NOC_Run5bHost.S_host (Tx := Tx) L copy std).Ctx := rfl
theorem args1_at (L : Library W (Nat → Record))
 (copy : Heap (Nat → Record) → Nat → Payload → S2W_TrustedStd.Outcome (Nat → Record))
 (std : S2W_TrustedStd.TrustedStd copy) (c : NOC_Run5bCtx.Ctx W Tx) :
 (S_host (Tx := Tx) L copy std).args1 c = NNE_EntryArgs.args c.i.entry 3 NPO_ProgramNov.verifier c.i.data := rfl
theorem args2_at (L : Library W (Nat → Record))
 (copy : Heap (Nat → Record) → Nat → Payload → S2W_TrustedStd.Outcome (Nat → Record))
 (std : S2W_TrustedStd.TrustedStd copy) (c : NOC_Run5bCtx.Ctx W Tx) :
 (S_host (Tx := Tx) L copy std).args2 c = NNE_EntryArgs.args c.j.entry 7 NPO_ProgramNov.verifier c.j.data := rfl
end AspisR1.NPO_Run5bHostNov
namespace AspisR1.NPO_FinalBNov
open Aeneas Aeneas.Std Result S2Trust S2W_D189Entry S2W_D189Wrappers
open RSL RSL.TAS RSL.TASB NNH_Libraries
open NNH_Run6Installed
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw
open FS FS2
variable {W Tx : Type}

theorem deployed_splitB
 (L0 : Library W (Nat → Record)) (borrow : S2TrustedSdkBorrow L0)
 (copy : Heap (Nat → Record) → Nat → Payload → S2W_TrustedStd.Outcome (Nat → Record))
 (std : S2W_TrustedStd.TrustedStd copy)
 (allocation217 : Bytes → Env → Bool) (allocation234 : TX2_234.Args → Env → Nat → Bool)
 (ch : NMX_R4_Authentication.Choices) (alloc2 : NMV_ConcreteWindows.Allocation)
 (fx : NOC_Run5bCtx.Fixed) (w : NOC_Run5bCtx.World W Tx)
 (H : AspisV8R19.DuplexFrames.Bytes → AspisV8R19.SourceDuplexStep.State)
 (queries : (NPO_Nov.AspisR1.NNH8_Exec.exec (Tx := Tx) L0 copy std).QueriesF fx)
 (run : Runs (NPO_Nov.AspisR1.NOC_Run5bHost.S_host (Tx := Tx) L0 copy std)
  (NPO_Nov.AspisR1.NNH_Run6Installed.implementation allocation217 allocation234 ch NNG_Candidate344.allocation alloc2)
  (ctxB (NPO_Nov.AspisR1.NNH8_Exec.exec (Tx := Tx) L0 copy std) fx w H)) :
 let c := ctxB (NPO_Nov.AspisR1.NNH8_Exec.exec (Tx := Tx) L0 copy std) fx w H
 (NPO_Nov.AspisR1.NOC_Run5bHost.S_host (Tx := Tx) L0 copy std).Bound c
  ((NPO_Nov.AspisR1.NOC_Run5bHost.S_host (Tx := Tx) L0 copy std).model1 c) ((NPO_Nov.AspisR1.NOC_Run5bHost.S_host (Tx := Tx) L0 copy std).model2 c) ∧
 NPO_Nov.AspisR1.NNH8_Split.rest L0 copy c ((NPO_Nov.AspisR1.NOC_Run5bHost.S_host (Tx := Tx) L0 copy std).model1 c)
  ((NPO_Nov.AspisR1.NOC_Run5bHost.S_host (Tx := Tx) L0 copy std).model2 c) ∧
 ((NPO_Nov.AspisR1.NNH8_HeadlineB.headlineB L0 borrow copy std).OutcomeRec c
  ((NPO_Nov.AspisR1.NOC_Run5bHost.S_host (Tx := Tx) L0 copy std).model1 c) ((NPO_Nov.AspisR1.NOC_Run5bHost.S_host (Tx := Tx) L0 copy std).model2 c) ∨
  (NPO_Nov.AspisR1.NNH8_Exec.exec (Tx := Tx) L0 copy std).ERec fx H) :=
 NPO_Nov.AspisR1.TAS_FinalB.deployed_splitB L0 borrow copy std allocation217 allocation234 ch alloc2 fx w H queries run

theorem fail_sub_rec
 (L0 : Library W (Nat → Record)) (borrow : S2TrustedSdkBorrow L0)
 (copy : Heap (Nat → Record) → Nat → Payload → S2W_TrustedStd.Outcome (Nat → Record))
 (std : S2W_TrustedStd.TrustedStd copy)
 (allocation217 : RSL.Bytes → Env → Bool) (allocation234 : TX2_234.Args → Env → Nat → Bool)
 (ch : NMX_R4_Authentication.Choices) (alloc2 : NMV_ConcreteWindows.Allocation)
 (fx : NOC_Run5bCtx.Fixed)
 (queries : (NPO_Nov.AspisR1.NNH8_Exec.exec (Tx := Tx) L0 copy std).QueriesF fx)
 (wOf : (AspisV8R19.DuplexFrames.Bytes → AspisV8R19.SourceDuplexStep.State) → NOC_Run5bCtx.World W Tx)
 (H : AspisV8R19.DuplexFrames.Bytes → AspisV8R19.SourceDuplexStep.State)
 (fail : Runs (NPO_Nov.AspisR1.NOC_Run5bHost.S_host (Tx := Tx) L0 copy std)
  (NPO_Nov.AspisR1.NNH_Run6Installed.implementation allocation217 allocation234 ch NNG_Candidate344.allocation alloc2)
  (ctxB (NPO_Nov.AspisR1.NNH8_Exec.exec (Tx := Tx) L0 copy std) fx (wOf H) H) ∧
 ¬ (NPO_Nov.AspisR1.NNH8_HeadlineB.headlineB L0 borrow copy std).OutcomeRec
  (ctxB (NPO_Nov.AspisR1.NNH8_Exec.exec (Tx := Tx) L0 copy std) fx (wOf H) H)
  ((NPO_Nov.AspisR1.NOC_Run5bHost.S_host (Tx := Tx) L0 copy std).model1 (ctxB (NPO_Nov.AspisR1.NNH8_Exec.exec (Tx := Tx) L0 copy std) fx (wOf H) H))
  ((NPO_Nov.AspisR1.NOC_Run5bHost.S_host (Tx := Tx) L0 copy std).model2 (ctxB (NPO_Nov.AspisR1.NNH8_Exec.exec (Tx := Tx) L0 copy std) fx (wOf H) H))) :
 (NPO_Nov.AspisR1.NNH8_Exec.exec (Tx := Tx) L0 copy std).ERec fx H :=
 NPO_Nov.AspisR1.TAS_FinalB.fail_sub_rec L0 borrow copy std allocation217 allocation234 ch alloc2 fx queries wOf H fail

theorem deployed_charge
 (L0 : Library W (Nat → Record)) (borrow : S2TrustedSdkBorrow L0)
 (copy : Heap (Nat → Record) → Nat → Payload → S2W_TrustedStd.Outcome (Nat → Record))
 (std : S2W_TrustedStd.TrustedStd copy)
 (allocation217 : RSL.Bytes → Env → Bool) (allocation234 : TX2_234.Args → Env → Nat → Bool)
 (ch : NMX_R4_Authentication.Choices) (alloc2 : NMV_ConcreteWindows.Allocation)
 (fx : NOC_Run5bCtx.Fixed) (anchor : AspisV8R19.DuplexFrames.Bytes → AspisV8R19.SourceDuplexStep.State)
 (queries : (NPO_Nov.AspisR1.NNH8_Exec.exec (Tx := Tx) L0 copy std).QueriesF fx)
 (wOf : (AspisV8R19.DuplexFrames.Bytes → AspisV8R19.SourceDuplexStep.State) → NOC_Run5bCtx.World W Tx) :
 (∀ H, max (0:Rat) (ind (Runs (NPO_Nov.AspisR1.NOC_Run5bHost.S_host (Tx := Tx) L0 copy std)
  (NPO_Nov.AspisR1.NNH_Run6Installed.implementation allocation217 allocation234 ch NNG_Candidate344.allocation alloc2)
  (ctxB (NPO_Nov.AspisR1.NNH8_Exec.exec (Tx := Tx) L0 copy std) fx (wOf H) H) ∧
 ¬ (NPO_Nov.AspisR1.NNH8_HeadlineB.headlineB L0 borrow copy std).OutcomeRec
  (ctxB (NPO_Nov.AspisR1.NNH8_Exec.exec (Tx := Tx) L0 copy std) fx (wOf H) H)
  ((NPO_Nov.AspisR1.NOC_Run5bHost.S_host (Tx := Tx) L0 copy std).model1 (ctxB (NPO_Nov.AspisR1.NNH8_Exec.exec (Tx := Tx) L0 copy std) fx (wOf H) H))
  ((NPO_Nov.AspisR1.NOC_Run5bHost.S_host (Tx := Tx) L0 copy std).model2 (ctxB (NPO_Nov.AspisR1.NNH8_Exec.exec (Tx := Tx) L0 copy std) fx (wOf H) H)))) ≤
  ind (BinRawByteCollisionTargets.event SelectedTranscriptParams.params.iv (fx.Q0+fx.Q1+2965)
   (eval H (AspisR1.NNH8_RecorderFixed.fixedProgram copy fx anchor)))) ∧
 lazyMean (AspisR1.NNH8_RecorderFixed.fixedProgram copy fx anchor) emptyTable
  (fun v => AspisV8R19.CausalFirstHitUnionBound.indicator
   (BinRawByteCollisionTargets.event SelectedTranscriptParams.params.iv (fx.Q0+fx.Q1+2965) v))
 ≤ F3T_Numeric.total (fx.Q0+fx.Q1) ∧
 (∀ H, let c := ctxB (NPO_Nov.AspisR1.NNH8_Exec.exec (Tx := Tx) L0 copy std) fx (wOf H) H
  F3T_RuntimeBound.failureModel (NPO_Nov.AspisR1.NOC_Run5bHost.runtime L0 copy c
   ((NPO_Nov.AspisR1.NOC_Run5bHost.S_host (Tx := Tx) L0 copy std).model1 c) ((NPO_Nov.AspisR1.NOC_Run5bHost.S_host (Tx := Tx) L0 copy std).model2 c)) ≤
  F3T_Numeric.total (fx.Q0+fx.Q1)) :=
 NPO_Nov.AspisR1.TAS_FinalB.deployed_charge L0 borrow copy std allocation217 allocation234 ch alloc2 fx anchor queries wOf
end AspisR1.NPO_FinalBNov
end
#print axioms NPO_DeployedIds.not_systemNov
#print axioms NPO_InstancesNov.D_eq
#print axioms AspisR1.NPO_Run5bHostNov.type_same
#print axioms AspisR1.NPO_Run5bHostNov.ctx_same
#print axioms AspisR1.NPO_Run5bHostNov.args1_at
#print axioms AspisR1.NPO_Run5bHostNov.args2_at
#print axioms AspisR1.NPO_FinalBNov.deployed_splitB
#print axioms AspisR1.NPO_FinalBNov.fail_sub_rec
#print axioms AspisR1.NPO_FinalBNov.deployed_charge
