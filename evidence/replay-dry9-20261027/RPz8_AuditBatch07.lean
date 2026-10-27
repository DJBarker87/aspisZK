import Lean
import RPz8_ART_WrapperBudget
import RPz8_ARW_LocalBudget
import RPz8_ARX_Cap
import RPz8_ARX_LocalCharge
import RPz8_ARX_SourceAlternative
import RPz8_ART_FullBudget
import RPz8_ARX_CachedCharge
import RPz8_ARX_RecoveryBranch
import RPz8_ARX_Join
import RPz8_ARX_Domination
import RPz8_ARU_Issued
import RPz8_ARU_OracleLog
import RPz8_ARU_Factory
import RPz8_ART_NativeAgreement
import RPz8_ARU_OriginalSupport
import RPz8_ART_NativeCertificate
import RPz8_ART_Cost
import RPz8_ART_Outcome
import RPz8_ART_OriginalLaw
import RPz8_ART_NativeCoverage
import RPz8_ART_QueriedCoverage
import RPz8_ARS_WorldCylinder
import RPz8_ARU_OriginalFactory
import RPz8_ARW_AdmittedSupport
import RPz8_ARX_TraceSupport
import RPz8_ARU_PartialFactory
import RPz8_ARU_Cuts
import RPz8_ARU_Checkpoint
import RPz8_ARU_R1
import RPz8_SCE_PublicProjection
import RPz8_ARS_Carrier
import RPz8_ARU_Carrier
import RPz8_ARW_Carrier
import RPz8_ARW_AdmittedQueries
import RPz8_ARU_FullSourceAlternative
import RPz8_ARU_Charge
import RPz8_ARU_RecoveryBranch
import RPz8_ARU_Join
import RPz8_ARU_AllWorld
import RPz8_ARU_CoverageQuantifiers
import RPz8_ARV_Poison
import RPz8_ARV_PoisonNative
import RPz8_ARV_NativePartial
import RPz8_ARV_Constant
import RPz8_ARW_DisconnectedAdmissions
import RPz8_ARW_RuntimeDomain
import RPz8_ARX_AdmittedRuntime
import RPz8_ARW_AdmittedBudget
import RPz8_ARU_RuntimeMass
import RPz8_ARX_Mass
import RPz8_ARX_SubmissionBudget
import RPz8_ARX_Residual
import RPz8_ARW_Core
import RPz8_ARW_Observations
import RPz8_ARX_Root
open Lean Elab Command
run_cmd do
  let env ← getEnv
  let selected : Array Name := #[ `RPz8_ART_WrapperBudget, `RPz8_ARW_LocalBudget, `RPz8_ARX_Cap, `RPz8_ARX_LocalCharge, `RPz8_ARX_SourceAlternative, `RPz8_ART_FullBudget, `RPz8_ARX_CachedCharge, `RPz8_ARX_RecoveryBranch, `RPz8_ARX_Join, `RPz8_ARX_Domination, `RPz8_ARU_Issued, `RPz8_ARU_OracleLog, `RPz8_ARU_Factory, `RPz8_ART_NativeAgreement, `RPz8_ARU_OriginalSupport, `RPz8_ART_NativeCertificate, `RPz8_ART_Cost, `RPz8_ART_Outcome, `RPz8_ART_OriginalLaw, `RPz8_ART_NativeCoverage, `RPz8_ART_QueriedCoverage, `RPz8_ARS_WorldCylinder, `RPz8_ARU_OriginalFactory, `RPz8_ARW_AdmittedSupport, `RPz8_ARX_TraceSupport, `RPz8_ARU_PartialFactory, `RPz8_ARU_Cuts, `RPz8_ARU_Checkpoint, `RPz8_ARU_R1, `RPz8_SCE_PublicProjection, `RPz8_ARS_Carrier, `RPz8_ARU_Carrier, `RPz8_ARW_Carrier, `RPz8_ARW_AdmittedQueries, `RPz8_ARU_FullSourceAlternative, `RPz8_ARU_Charge, `RPz8_ARU_RecoveryBranch, `RPz8_ARU_Join, `RPz8_ARU_AllWorld, `RPz8_ARU_CoverageQuantifiers, `RPz8_ARV_Poison, `RPz8_ARV_PoisonNative, `RPz8_ARV_NativePartial, `RPz8_ARV_Constant, `RPz8_ARW_DisconnectedAdmissions, `RPz8_ARW_RuntimeDomain, `RPz8_ARX_AdmittedRuntime, `RPz8_ARW_AdmittedBudget, `RPz8_ARU_RuntimeMass, `RPz8_ARX_Mass, `RPz8_ARX_SubmissionBudget, `RPz8_ARX_Residual, `RPz8_ARW_Core, `RPz8_ARW_Observations, `RPz8_ARX_Root ]
  for i in [:env.header.modules.size] do
    let owner := env.header.modules[i]!.module
    let data := env.header.moduleData[i]!
    if selected.contains owner then
      logInfo m!"RPZ8_IMPORTS {(Json.mkObj [("module", toJson owner.toString), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
  let mut count : Nat := 0
  for (n, _) in env.toKernelEnv.constants.toList do
    if let some mi := env.getModuleIdxFor? n then
      let owner := env.header.modules[mi.toNat]!.module
      if selected.contains owner then
        let axs ← collectAxioms n
        logInfo m!"RPZ8_DECL {(Json.mkObj [("module", toJson owner.toString), ("name", toJson n.toString), ("axioms", toJson (axs.map Name.toString))]).compress}"
        elabCommand (← `(#print axioms $(mkIdent n)))
        count := count + 1
  logInfo m!"RPZ8_AUDIT_COMPLETE declarations={count} modules={selected.size}"
