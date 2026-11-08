import NNM_COMBINED_IMPORT
import TAS_Top
import NVR_COMBINED_IMPORT
import NVR_Carrier
import NVR_DispatchEmitted
import NVR_Reify
import NVR_NNCWeak
import FIN_COMBINED_IMPORT
set_option autoImplicit false
noncomputable section
namespace NNO_StatementChecks
open RSL

def statementOf {P : Prop} (_ : P) : Prop := P

theorem statement240 (a2 : NMV_ConcreteWindows.Allocation) (ch : NMX_R4_Authentication.Choices) :
 statementOf (FIN_240.candidate ch a2) =
 TX2_240.RowSpec_240 LIBB_PoolLib.library LIBB_PoolLib.deployed LIBB_V2Star.library
  (NMV_ConcreteWindows.stage2 a2 (NMX_R9_StageTwo.stage2 ch)) := rfl

theorem statement221 (a2 : NMV_ConcreteWindows.Allocation) (ch : NMX_R4_Authentication.Choices) :
 statementOf (FIN_221.candidate ch a2) =
 TX2_221.RowSpec_221 LIBB_PoolLib.library LIBB_PoolLib.deployed LIBB_V2Star.library
  (TX1_344.asStage1 LIB_Instances.VL LIB_Instances.P LIB_Instances.C)
  (NVR_Dispatch.process AspisR1.NNG_Candidate344.producer (FIN_240.producer ch a2)) := rfl

theorem statement333 (a2 : NMV_ConcreteWindows.Allocation) (ch : NMX_R4_Authentication.Choices) :
 statementOf (FIN_333.candidate ch a2) =
 TX1_333.RowSpec_333 LIBB_PoolLib.library LIBB_PoolLib.deployed LIBB_V2Star.library
  LIB_Instances.VL LIB_Instances.P LIB_Instances.C
  (NVR_Dispatch.process AspisR1.NNG_Candidate344.producer (FIN_240.producer ch a2)) := rfl

theorem statement213 (a2 : NMV_ConcreteWindows.Allocation) (ch : NMX_R4_Authentication.Choices) :
 statementOf (FIN_213.candidate ch a2) =
 TX2_213.RowSpec_213 LIBB_PoolLib.library LIBB_PoolLib.deployed LIBB_V2Star.library
  (TX1_344.asStage1 LIB_Instances.VL LIB_Instances.P LIB_Instances.C)
  (NVR_Dispatch.entry (NVR_Dispatch.process AspisR1.NNG_Candidate344.producer
   (FIN_240.producer ch a2))) := rfl

theorem statement330 (a2 : NMV_ConcreteWindows.Allocation) (ch : NMX_R4_Authentication.Choices) :
 statementOf (FIN_330.candidate ch a2) =
 TX1_330.RowSpec_330 LIBB_PoolLib.library LIBB_PoolLib.deployed LIBB_V2Star.library
  LIB_Instances.VL LIB_Instances.P LIB_Instances.C
  (NVR_Dispatch.entry (NVR_Dispatch.process AspisR1.NNG_Candidate344.producer
   (FIN_240.producer ch a2))) := rfl

theorem child240 (a2 : NMV_ConcreteWindows.Allocation) (ch : NMX_R4_Authentication.Choices) :
 FIN_240.producer ch a2 = NMV_ConcreteWindows.stage2 a2 (NMX_R9_StageTwo.stage2 ch) := rfl

theorem child344 : AspisR1.NNG_Candidate344.producer =
 NMV_ConcreteWindows.stage1 AspisR1.NNG_Candidate344.allocation
  AspisR1.NNG_TotalProducer345.producer := rfl

theorem process221 (a2 : NMV_ConcreteWindows.Allocation) (ch : NMX_R4_Authentication.Choices) :
 FIN_221.producer ch a2 = NVR_Dispatch.process AspisR1.NNG_Candidate344.producer
  (FIN_240.producer ch a2) := rfl

theorem process333 (a2 : NMV_ConcreteWindows.Allocation) (ch : NMX_R4_Authentication.Choices) :
 FIN_333.producer ch a2 = NVR_Dispatch.process AspisR1.NNG_Candidate344.producer
  (FIN_240.producer ch a2) := rfl

theorem deployed_same : LIBB_PoolLib.deployed = LIB_Instances.D := rfl

def installed (ch : NMX_R4_Authentication.Choices) (a2 : NMV_ConcreteWindows.Allocation)
 (I : TAS.Impl LIBB_PoolLib.library LIBB_V2Star.library LIB_Instances.VL) :=
 { I with process := FIN_333.producer ch a2, entry := FIN_330.producer ch a2 }

theorem tas333 (a2 : NMV_ConcreteWindows.Allocation) (ch : NMX_R4_Authentication.Choices)
 (I : TAS.Impl LIBB_PoolLib.library LIBB_V2Star.library LIB_Instances.VL) :
 TX1_333.RowSpec_333 LIBB_PoolLib.library LIBB_PoolLib.deployed LIBB_V2Star.library
  LIB_Instances.VL LIB_Instances.P LIB_Instances.C (FIN_333.producer ch a2) =
 TX2_221.RowSpec_221 LIBB_PoolLib.library LIBB_PoolLib.deployed LIBB_V2Star.library
  (TX1_344.asStage1 LIB_Instances.VL LIB_Instances.P LIB_Instances.C) (FIN_221.producer ch a2) :=
 TAS.row333_is_221 (L := LIBB_PoolLib.library) (D := LIBB_PoolLib.deployed)
  (VL := LIB_Instances.VL) (P := LIB_Instances.P) (C := LIB_Instances.C)
  (I := installed ch a2 I) LIBB_V2Star.library

theorem tas330 (a2 : NMV_ConcreteWindows.Allocation) (ch : NMX_R4_Authentication.Choices)
 (I : TAS.Impl LIBB_PoolLib.library LIBB_V2Star.library LIB_Instances.VL) :
 TX1_330.RowSpec_330 LIBB_PoolLib.library LIBB_PoolLib.deployed LIBB_V2Star.library
  LIB_Instances.VL LIB_Instances.P LIB_Instances.C (FIN_330.producer ch a2) =
 TX2_213.RowSpec_213 LIBB_PoolLib.library LIBB_PoolLib.deployed LIBB_V2Star.library
  (TX1_344.asStage1 LIB_Instances.VL LIB_Instances.P LIB_Instances.C) (FIN_213.producer ch a2) :=
 TAS.row330_is_213 (L := LIBB_PoolLib.library) (D := LIBB_PoolLib.deployed)
  (VL := LIB_Instances.VL) (P := LIB_Instances.P) (C := LIB_Instances.C)
  (I := installed ch a2 I) LIBB_V2Star.library

#print axioms statement240
#print axioms statement221
#print axioms statement333
#print axioms statement213
#print axioms statement330
#print axioms child240
#print axioms child344
#print axioms process221
#print axioms process333
#print axioms deployed_same
#print axioms tas333
#print axioms tas330
#print axioms NVR_NoWritePool.ofCloned_free
#print axioms NVR_NoWritePool.data_free
#print axioms NVR_NoWritePool.verifierCheckpoint_free
end NNO_StatementChecks
end

open Lean Elab Command
set_option pp.all true
run_cmd do
 let env := (← getEnv).setExporting false
 let roots : Array Name := #[`NVR_Folds.process_ref,`NVR_Folds.process_tx1,`NVR_Folds.process_tx2,`NVR_Folds.entry_tx2,`NVR_Folds.entry_tx1,`NVR_DispatchEmitted.process_emitted,`NVR_DispatchEmitted.entry_emitted,`NVR_TasRoots.children_same,`NVR_TasRoots.field240,`NVR_TasRoots.field344,`NVR_TasRoots.weak240,`NVR_TasRoots.weakFrame,`NVR_NoWrite241.error_free,`NVR_NoWrite241.owned241_free,`NVR_NNCWeak.weak240,`NVR_NNCWeak.frame,`NVR_NNCWeak.sdk,`NVR_NoWriteOwned.auth_body_free,`NVR_NoWriteOwned.auth_free,`NVR_NoWriteOwned.validate_free,`NVR_G2Reference.reference_free,`NVR_G2Reference.frame,`NVR_Carrier.byte_inverse,`NVR_Carrier.unbyte_inverse,`NVR_Carrier.bytes_inverse,`NVR_Carrier.unbytes_inverse,`NVR_Carrier.unbytes_eq_iff,`NVR_Carrier.stage1_iff,`NVR_Carrier.asq8_iff,`NVR_Combined.composed_nmw,`NVR_NoWritePool.ofCloned_free,`NVR_NoWritePool.data_free,`NVR_NoWritePool.verifierCheckpoint_free,`NVR_NoWritePool.pda_free,`NVR_NoWritePool.master_free,`NVR_NoWritePool.checkpoint_free,`NVR_NoWritePool.lane_free,`NVR_NoWritePool.registry_immutable_free,`NVR_NoWritePool.registry_v1_free,`NVR_NoWritePool.registry_free,`NVR_Reify.args_inverse,`NVR_Reify.process_source,`NVR_Reify.entry_source,`NVR_CandidateRoots.root344,`NVR_CandidateRoots.root240,`NVR_TAS.r221,`NVR_TAS.r213,`NVR_TAS.roots,`NVR_TAS.weak_process,`NVR_TAS.weak_entry,`NVR_Dispatch.admitted_iff]
 for name in roots do
  let some c := env.find? name | throwError "missing root {name}"
  if true then
   let some idx := env.getModuleIdxFor? name | throwError "missing owner {name}"
   let statement ← liftTermElabM (PrettyPrinter.ppExpr c.type)
   let row := Json.mkObj [("root",toJson name.toString),("owner_module",toJson env.header.moduleNames[idx]!.toString),("obligation_statement",toJson statement.pretty)]
   logInfo m!"NNO_OWNER {row.compress}"
