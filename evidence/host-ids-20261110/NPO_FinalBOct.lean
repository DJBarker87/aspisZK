import NPO_CloneOct
set_option autoImplicit false
noncomputable section
namespace NPO_ProgramOct
open Aeneas Aeneas.Std
/-- CPH_Program.verifier with the id replaced by the Oct deployment's verifier id. -/
abbrev verifier : AspisR1.S2W_ExtractionBoundary.Program := NPO_DeployedIds.verifierOct
end NPO_ProgramOct
namespace NPO_InstancesOct
/-- LIB_Instances.D with the Pool/registry ids replaced (the kernel-checked clone). -/
abbrev D : RSL.DeployedIds := NPO_Oct.LIB_Instances.D
theorem D_eq : D = NPO_DeployedIds.DOct := rfl
/-- The 29 October D is the already-pinned LIB_Deployed.devnet. -/
theorem D_devnet : D = LIB_Deployed.devnet := rfl
end NPO_InstancesOct
namespace AspisR1.NPO_Run5bHostOct
open Aeneas Aeneas.Std Result S2Trust S2W_D189Entry S2W_D189Wrappers
open RSL RSL.TAS RSL.TASB NNH_Libraries
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep AspisV8R19.MemoizedProgramLaw
variable {W Tx : Type}
/-- NOC_Run5bHost.S_host built by the same construction at the Oct ids. -/
abbrev S_host := @NPO_Oct.AspisR1.NOC_Run5bHost.S_host
theorem type_same : type_of% @S_host = type_of% @AspisR1.NOC_Run5bHost.S_host := rfl
theorem ctx_same (L : Library W (Nat → Record))
 (copy : Heap (Nat → Record) → Nat → Payload → S2W_TrustedStd.Outcome (Nat → Record))
 (std : S2W_TrustedStd.TrustedStd copy) :
 (S_host (Tx := Tx) L copy std).Ctx = (AspisR1.NOC_Run5bHost.S_host (Tx := Tx) L copy std).Ctx := rfl
theorem args1_at (L : Library W (Nat → Record))
 (copy : Heap (Nat → Record) → Nat → Payload → S2W_TrustedStd.Outcome (Nat → Record))
 (std : S2W_TrustedStd.TrustedStd copy) (c : NOC_Run5bCtx.Ctx W Tx) :
 (S_host (Tx := Tx) L copy std).args1 c = NNE_EntryArgs.args c.i.entry 3 NPO_ProgramOct.verifier c.i.data := rfl
theorem args2_at (L : Library W (Nat → Record))
 (copy : Heap (Nat → Record) → Nat → Payload → S2W_TrustedStd.Outcome (Nat → Record))
 (std : S2W_TrustedStd.TrustedStd copy) (c : NOC_Run5bCtx.Ctx W Tx) :
 (S_host (Tx := Tx) L copy std).args2 c = NNE_EntryArgs.args c.j.entry 7 NPO_ProgramOct.verifier c.j.data := rfl
end AspisR1.NPO_Run5bHostOct
namespace AspisR1.NPO_FinalBOct
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
 (queries : (NPO_Oct.AspisR1.NNH8_Exec.exec (Tx := Tx) L0 copy std).QueriesF fx)
 (run : Runs (NPO_Oct.AspisR1.NOC_Run5bHost.S_host (Tx := Tx) L0 copy std)
  (NPO_Oct.AspisR1.NNH_Run6Installed.implementation allocation217 allocation234 ch NNG_Candidate344.allocation alloc2)
  (ctxB (NPO_Oct.AspisR1.NNH8_Exec.exec (Tx := Tx) L0 copy std) fx w H)) :
 let c := ctxB (NPO_Oct.AspisR1.NNH8_Exec.exec (Tx := Tx) L0 copy std) fx w H
 (NPO_Oct.AspisR1.NOC_Run5bHost.S_host (Tx := Tx) L0 copy std).Bound c
  ((NPO_Oct.AspisR1.NOC_Run5bHost.S_host (Tx := Tx) L0 copy std).model1 c) ((NPO_Oct.AspisR1.NOC_Run5bHost.S_host (Tx := Tx) L0 copy std).model2 c) ∧
 NPO_Oct.AspisR1.NNH8_Split.rest L0 copy c ((NPO_Oct.AspisR1.NOC_Run5bHost.S_host (Tx := Tx) L0 copy std).model1 c)
  ((NPO_Oct.AspisR1.NOC_Run5bHost.S_host (Tx := Tx) L0 copy std).model2 c) ∧
 ((NPO_Oct.AspisR1.NNH8_HeadlineB.headlineB L0 borrow copy std).OutcomeRec c
  ((NPO_Oct.AspisR1.NOC_Run5bHost.S_host (Tx := Tx) L0 copy std).model1 c) ((NPO_Oct.AspisR1.NOC_Run5bHost.S_host (Tx := Tx) L0 copy std).model2 c) ∨
  (NPO_Oct.AspisR1.NNH8_Exec.exec (Tx := Tx) L0 copy std).ERec fx H) :=
 NPO_Oct.AspisR1.TAS_FinalB.deployed_splitB L0 borrow copy std allocation217 allocation234 ch alloc2 fx w H queries run

theorem fail_sub_rec
 (L0 : Library W (Nat → Record)) (borrow : S2TrustedSdkBorrow L0)
 (copy : Heap (Nat → Record) → Nat → Payload → S2W_TrustedStd.Outcome (Nat → Record))
 (std : S2W_TrustedStd.TrustedStd copy)
 (allocation217 : RSL.Bytes → Env → Bool) (allocation234 : TX2_234.Args → Env → Nat → Bool)
 (ch : NMX_R4_Authentication.Choices) (alloc2 : NMV_ConcreteWindows.Allocation)
 (fx : NOC_Run5bCtx.Fixed)
 (queries : (NPO_Oct.AspisR1.NNH8_Exec.exec (Tx := Tx) L0 copy std).QueriesF fx)
 (wOf : (AspisV8R19.DuplexFrames.Bytes → AspisV8R19.SourceDuplexStep.State) → NOC_Run5bCtx.World W Tx)
 (H : AspisV8R19.DuplexFrames.Bytes → AspisV8R19.SourceDuplexStep.State)
 (fail : Runs (NPO_Oct.AspisR1.NOC_Run5bHost.S_host (Tx := Tx) L0 copy std)
  (NPO_Oct.AspisR1.NNH_Run6Installed.implementation allocation217 allocation234 ch NNG_Candidate344.allocation alloc2)
  (ctxB (NPO_Oct.AspisR1.NNH8_Exec.exec (Tx := Tx) L0 copy std) fx (wOf H) H) ∧
 ¬ (NPO_Oct.AspisR1.NNH8_HeadlineB.headlineB L0 borrow copy std).OutcomeRec
  (ctxB (NPO_Oct.AspisR1.NNH8_Exec.exec (Tx := Tx) L0 copy std) fx (wOf H) H)
  ((NPO_Oct.AspisR1.NOC_Run5bHost.S_host (Tx := Tx) L0 copy std).model1 (ctxB (NPO_Oct.AspisR1.NNH8_Exec.exec (Tx := Tx) L0 copy std) fx (wOf H) H))
  ((NPO_Oct.AspisR1.NOC_Run5bHost.S_host (Tx := Tx) L0 copy std).model2 (ctxB (NPO_Oct.AspisR1.NNH8_Exec.exec (Tx := Tx) L0 copy std) fx (wOf H) H))) :
 (NPO_Oct.AspisR1.NNH8_Exec.exec (Tx := Tx) L0 copy std).ERec fx H :=
 NPO_Oct.AspisR1.TAS_FinalB.fail_sub_rec L0 borrow copy std allocation217 allocation234 ch alloc2 fx queries wOf H fail

theorem deployed_charge
 (L0 : Library W (Nat → Record)) (borrow : S2TrustedSdkBorrow L0)
 (copy : Heap (Nat → Record) → Nat → Payload → S2W_TrustedStd.Outcome (Nat → Record))
 (std : S2W_TrustedStd.TrustedStd copy)
 (allocation217 : RSL.Bytes → Env → Bool) (allocation234 : TX2_234.Args → Env → Nat → Bool)
 (ch : NMX_R4_Authentication.Choices) (alloc2 : NMV_ConcreteWindows.Allocation)
 (fx : NOC_Run5bCtx.Fixed) (anchor : AspisV8R19.DuplexFrames.Bytes → AspisV8R19.SourceDuplexStep.State)
 (queries : (NPO_Oct.AspisR1.NNH8_Exec.exec (Tx := Tx) L0 copy std).QueriesF fx)
 (wOf : (AspisV8R19.DuplexFrames.Bytes → AspisV8R19.SourceDuplexStep.State) → NOC_Run5bCtx.World W Tx) :
 (∀ H, max (0:Rat) (ind (Runs (NPO_Oct.AspisR1.NOC_Run5bHost.S_host (Tx := Tx) L0 copy std)
  (NPO_Oct.AspisR1.NNH_Run6Installed.implementation allocation217 allocation234 ch NNG_Candidate344.allocation alloc2)
  (ctxB (NPO_Oct.AspisR1.NNH8_Exec.exec (Tx := Tx) L0 copy std) fx (wOf H) H) ∧
 ¬ (NPO_Oct.AspisR1.NNH8_HeadlineB.headlineB L0 borrow copy std).OutcomeRec
  (ctxB (NPO_Oct.AspisR1.NNH8_Exec.exec (Tx := Tx) L0 copy std) fx (wOf H) H)
  ((NPO_Oct.AspisR1.NOC_Run5bHost.S_host (Tx := Tx) L0 copy std).model1 (ctxB (NPO_Oct.AspisR1.NNH8_Exec.exec (Tx := Tx) L0 copy std) fx (wOf H) H))
  ((NPO_Oct.AspisR1.NOC_Run5bHost.S_host (Tx := Tx) L0 copy std).model2 (ctxB (NPO_Oct.AspisR1.NNH8_Exec.exec (Tx := Tx) L0 copy std) fx (wOf H) H)))) ≤
  ind (BinRawByteCollisionTargets.event SelectedTranscriptParams.params.iv (fx.Q0+fx.Q1+2965)
   (eval H (AspisR1.NNH8_RecorderFixed.fixedProgram copy fx anchor)))) ∧
 lazyMean (AspisR1.NNH8_RecorderFixed.fixedProgram copy fx anchor) emptyTable
  (fun v => AspisV8R19.CausalFirstHitUnionBound.indicator
   (BinRawByteCollisionTargets.event SelectedTranscriptParams.params.iv (fx.Q0+fx.Q1+2965) v))
 ≤ F3T_Numeric.total (fx.Q0+fx.Q1) ∧
 (∀ H, let c := ctxB (NPO_Oct.AspisR1.NNH8_Exec.exec (Tx := Tx) L0 copy std) fx (wOf H) H
  F3T_RuntimeBound.failureModel (NPO_Oct.AspisR1.NOC_Run5bHost.runtime L0 copy c
   ((NPO_Oct.AspisR1.NOC_Run5bHost.S_host (Tx := Tx) L0 copy std).model1 c) ((NPO_Oct.AspisR1.NOC_Run5bHost.S_host (Tx := Tx) L0 copy std).model2 c)) ≤
  F3T_Numeric.total (fx.Q0+fx.Q1)) :=
 NPO_Oct.AspisR1.TAS_FinalB.deployed_charge L0 borrow copy std allocation217 allocation234 ch alloc2 fx anchor queries wOf
end AspisR1.NPO_FinalBOct
end
#print axioms NPO_DeployedIds.not_systemOct
#print axioms NPO_InstancesOct.D_eq
#print axioms NPO_InstancesOct.D_devnet
#print axioms AspisR1.NPO_Run5bHostOct.type_same
#print axioms AspisR1.NPO_Run5bHostOct.ctx_same
#print axioms AspisR1.NPO_Run5bHostOct.args1_at
#print axioms AspisR1.NPO_Run5bHostOct.args2_at
#print axioms AspisR1.NPO_FinalBOct.deployed_splitB
#print axioms AspisR1.NPO_FinalBOct.fail_sub_rec
#print axioms AspisR1.NPO_FinalBOct.deployed_charge
