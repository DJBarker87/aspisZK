import Lean
import NP6_RecordShape
import NP6_ParsedClaims
import P6C_Accepted
import Hir_PartialOracle
import Hist_EntryZero
import Hist_ZeroHead
import Hist_ZeroReject
import Hist_InitialZero
import Hist_Store
import Hist_RuntimeEntry
import Hist_StepProtection
import Hist_TraceProtection
import Hist_Persistence
import Hist_SecondSnapshot
import Hist_CausalBinding
import Hiq_KeyLaw
import Hiq_ReleaseRoute
import Hiq_RuntimeWriter
import Hiq_NativeWriter
import Hiq_RuntimeAction
import Hiq_NativeAction
import Hiq_NativeClassify
import Hiq_NativeHistory
import Hist_P2Prime
import CPP_Second
import Hist_CommittedPayload
import PoolT_Verifier
import PoolT_CopyShape
import CPP_Metadata
import Hist_Nonvacuity
import CPP_BankCache
import Hist_TryGuard
import Hist_Asq8Guards
import Hist_ValidateCut
import Hist_Metadata
import Hist_ReaderAuthority
import Hist_SourceMarker
import Hist_WriterInitialized
import Hist_WriterShape
import Hiq_CausalVersion
import PoolT_Write
import CPP_TraceAppend
import SAF_AcceptedValue
import CPH_Program
import F3_Checkpoint
import F3_Counts
import F3T_Experiment
import F3T_Projection
import F3T_Charged
import F3T_Bounds
import F3T_Canon
import F3T_TwoPass
import F3T_Decision
import F3T_Trace
import F3T_Frame
import F3T_Reached
import F3T_Roots
import F3T_ActualChecks
import F3T_Admission
import F3T_CanonicalChecks
import F3T_Prefix
import F3T_Causal
import F3T_Checked
import F3T_CheckedView
import F3T_Tag
import F3T_AcceptedFacts
import F3T_Completion
import F3T_Accounting
import F3T_Clean
import F3T_Probability
import F3T_Cost
import F3T_ModelClaims
import F3T_AcceptedTransport
import F3T_Recovered
import F3U_Oracle
import F3U_ReifyValue
import F3U_ReifyLog
import F3U_ReifyExact
import F3U_Rehash
import F3U_RehashBind
import F3V_SampleBlock
import F3V_SemanticValidated
import F3V_Begin13
import F3V_Begin9
import F3V_Begin5
import F3V_Begin
import F3V_RoundStep
import F3V_Rounds
import F3V_CircleValidated
import F3V_SemanticFinish
import F3U_RehashInit
import F3U_RehashPublic
import F3V_SemanticVerify
import F3V_RehashCongr
import F3V_TranscriptNew
import F3V_TranscriptAbsorb
import F3V_TranscriptBlock
import F3V_Scalar
import F3V_Rho
import F3V_Queries

open Lean Elab Command

run_cmd do
  let env ← getEnv
  let selected : Array Name := #[ `NP6_RecordShape, `NP6_ParsedClaims, `P6C_Accepted, `Hir_PartialOracle, `Hist_EntryZero, `Hist_ZeroHead, `Hist_ZeroReject, `Hist_InitialZero, `Hist_Store, `Hist_RuntimeEntry, `Hist_StepProtection, `Hist_TraceProtection, `Hist_Persistence, `Hist_SecondSnapshot, `Hist_CausalBinding, `Hiq_KeyLaw, `Hiq_ReleaseRoute, `Hiq_RuntimeWriter, `Hiq_NativeWriter, `Hiq_RuntimeAction, `Hiq_NativeAction, `Hiq_NativeClassify, `Hiq_NativeHistory, `Hist_P2Prime, `CPP_Second, `Hist_CommittedPayload, `PoolT_Verifier, `PoolT_CopyShape, `CPP_Metadata, `Hist_Nonvacuity, `CPP_BankCache, `Hist_TryGuard, `Hist_Asq8Guards, `Hist_ValidateCut, `Hist_Metadata, `Hist_ReaderAuthority, `Hist_SourceMarker, `Hist_WriterInitialized, `Hist_WriterShape, `Hiq_CausalVersion, `PoolT_Write, `CPP_TraceAppend, `SAF_AcceptedValue, `CPH_Program, `F3_Checkpoint, `F3_Counts, `F3T_Experiment, `F3T_Projection, `F3T_Charged, `F3T_Bounds, `F3T_Canon, `F3T_TwoPass, `F3T_Decision, `F3T_Trace, `F3T_Frame, `F3T_Reached, `F3T_Roots, `F3T_ActualChecks, `F3T_Admission, `F3T_CanonicalChecks, `F3T_Prefix, `F3T_Causal, `F3T_Checked, `F3T_CheckedView, `F3T_Tag, `F3T_AcceptedFacts, `F3T_Completion, `F3T_Accounting, `F3T_Clean, `F3T_Probability, `F3T_Cost, `F3T_ModelClaims, `F3T_AcceptedTransport, `F3T_Recovered, `F3U_Oracle, `F3U_ReifyValue, `F3U_ReifyLog, `F3U_ReifyExact, `F3U_Rehash, `F3U_RehashBind, `F3V_SampleBlock, `F3V_SemanticValidated, `F3V_Begin13, `F3V_Begin9, `F3V_Begin5, `F3V_Begin, `F3V_RoundStep, `F3V_Rounds, `F3V_CircleValidated, `F3V_SemanticFinish, `F3U_RehashInit, `F3U_RehashPublic, `F3V_SemanticVerify, `F3V_RehashCongr, `F3V_TranscriptNew, `F3V_TranscriptAbsorb, `F3V_TranscriptBlock, `F3V_Scalar, `F3V_Rho, `F3V_Queries ]
  for i in [:env.header.modules.size] do
    let owner := env.header.modules[i]!.module
    let data := env.header.moduleData[i]!
    logInfo m!"RPZ5_IMPORTS {(Json.mkObj [("module", toJson owner.toString), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
  let mut count : Nat := 0
  for (n, c) in env.toKernelEnv.constants.toList do
    if let some mi := env.getModuleIdxFor? n then
      let owner := env.header.modules[mi.toNat]!.module
      if c.isAxiom then
        logInfo m!"RPZ5_AXIOM {(Json.mkObj [("module", toJson owner.toString), ("name", toJson n.toString)]).compress}"
      if selected.contains owner && n.hash.toNat % 1 == 0 then
        let debugPrefixes := #["AspisR1RecordParser.r1_wire.Error.Insts.CoreFmtDebug", "AspisR1PrefixAggregateParser.r1_wire.Error.Insts.CoreFmtDebug"]
        let refs := c.type.getUsedConstants ++ (((c.value? true).map (fun e => e.getUsedConstants)).getD #[])
        for ref in refs do
          if debugPrefixes.any (fun p => ref.toString == p || ref.toString.startsWith (p ++ ".")) then
            logInfo m!"RPZ5_DEBUG_REF {(Json.mkObj [("module", toJson owner.toString), ("name", toJson n.toString), ("reference", toJson ref.toString)]).compress}"
        let axs ← collectAxioms n
        logInfo m!"RPZ5_DECL {(Json.mkObj [("module", toJson owner.toString), ("name", toJson n.toString), ("axioms", toJson (axs.map Name.toString))]).compress}"
        elabCommand (← `(#print axioms $(mkIdent n)))
        count := count + 1
  logInfo m!"RPZ5_AUDIT_COMPLETE declarations={count} modules={selected.size}"
