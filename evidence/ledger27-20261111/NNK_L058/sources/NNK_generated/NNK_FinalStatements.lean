import NNK_COMBINED_IMPORT
import Lean
section NNK_Review
open AspisR1
example : RSL.TX1_137.RowSpec_137 LIB_VLib.library NNG_Producer137.producer := NNG_Candidate137.candidate
example (a : RSL.TX1_137.Args LIB_VLib.library) :
 RSL.TX1_137.Domain LIB_VLib.library a =
 (LIB_VLib.library.publicDom a.public_ ∧ LIB_VLib.library.semanticBytesDom a.bytes) := rfl
#print NNG_Candidate137.candidate
#print NNG_Producer137.producer
#print NNG_FinishOccurrence137.occurrence
#print NNG_Caller136From137.finish_domain
#print RSL.TX1_137.RowSpec_137
#print axioms NNG_Candidate137.candidate
#print axioms NNG_FinishOccurrence137.occurrence
#print axioms NNG_Candidate136.candidate
#print axioms RSL.TX1_137.rejects_constErr
example : RSL.TX1_087.RowSpec_087 LIB_Instances.VL LIB_Instances.P NNG_Producer087.producer := NNG_Candidate087.candidate
example (a : RSL.TX1_087.Args LIB_Instances.VL) (obs : RSL.Observer) :
 RSL.TX1_087.Domain LIB_Instances.VL a obs =
 (a.proof.length = RSL.VPROOF_BYTES ∧ obs = none ∧ LIB_Instances.VL.publicDom a.public_ ∧
 LIB_Instances.VL.checkValuesDom (RSL.slice a.proof RSL.OFF_Y1 RSL.OFF_INACTIVE)) := rfl
#print NNG_Candidate087.candidate
#print NNG_Producer087.producer
#print NNG_PreparedOccurrence087.occurrence
#print NNG_ReadyFront087.returned
#print RSL.TX1_087.RowSpec_087
#print LIB_Instances.VL
#print LIB_Instances.P
#print axioms NNG_Candidate087.candidate
#print axioms NNG_Producer087.source
#print axioms NNG_PreparedOccurrence087.occurrence
#print axioms RSL.TX1_087.domain_needs_R4
#print axioms RSL.TX1_087.rejects_wrong_g
example (allocations : RSL.TX2_234.Args → RSL.Env → Nat → Bool) :
 RSL.TX2_234.RowSpec_234 LIBB_PoolLib.library LIBB_PoolLib.deployed (NMX_R3_RegistryRoot.authenticate allocations) := NMX_R3_RegistryRoot.root allocations
example (allocationSucceeded : RSL.Bytes → RSL.Env → Bool) :
 RSL.TX2_217.RowSpec_217 (NMX_R3_DecoderFold.decode allocationSucceeded) := NMX_R3_DecoderFold.root allocationSucceeded
#print RSL.TX2_234.RowSpec_234
#print NMX_R3_RegistryRoot.root
#print NMX_R3_RegistryRoot.authenticate
#print NMX_R3_RegistryProjectionRef.reference
#print NMX_R3_RegistryNativeFold.native
#print NMX_R3_RegistryIds.pool
#print NMX_R3_RegistryIds.registry
#print RSL.TX2_217.RowSpec_217
#print NMX_R3_DecoderFold.root
#print NMX_R3_DecoderFold.complete
#print axioms NMX_R3_RegistryRoot.root
#print axioms NMX_R3_DecoderFold.root
example (a : RSL.TX2_234.Args) : RSL.TX2_234.Domain a = True := rfl
example (bytes : RSL.Bytes) : RSL.TX2_217.Domain bytes = True := rfl
#print axioms RSL.TX2_234.rejects_constAbort
end NNK_Review
open Lean Elab Command
set_option pp.all true
run_cmd do
  let manifest ← IO.ofExcept (Json.parse (← IO.FS.readFile "NNK_AUDIT_ROOTS.json"))
  let roots ← IO.ofExcept (manifest.getObjValAs? (Array String) "roots")
  let env := (← getEnv).setExporting false
  for root in roots do
    let declName := root.toName
    let some c := env.find? declName | throwError "missing required root {root}"
    let some idx := env.getModuleIdxFor? declName | throwError "missing owner {root}"
    let statement ← liftTermElabM (PrettyPrinter.ppExpr c.type)
    let row := Json.mkObj [("root",toJson root),
      ("owner_module",toJson env.header.moduleNames[idx]!.toString),
      ("obligation_statement",toJson statement.pretty)]
    logInfo m!"NNK_OWNER {row.compress}"
