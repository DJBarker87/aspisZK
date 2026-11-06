import NKH_COMBINED_IMPORT
import Lean
open Lean Elab Command
set_option pp.all true
#print NJZ_Weights.new_source
#print axioms NJZ_Weights.new_source
#print NJZ_CodecSemantics.root
#print axioms NJZ_CodecSemantics.root
#print NJZ_CodecSemantics.source
#print axioms NJZ_CodecSemantics.source
#print NJZ_CodecSemantics.domain
#print axioms NJZ_CodecSemantics.domain
#print NJZ_TreeParent.source
#print axioms NJZ_TreeParent.source
#print NJZ_PoolRoot.default
#print axioms NJZ_PoolRoot.default
#print NJZ_PoolRoot.empty
#print axioms NJZ_PoolRoot.empty
#print NJZ_PoolRoot.roots
#print axioms NJZ_PoolRoot.roots
#print NJZ_PoolRoot.domains
#print axioms NJZ_PoolRoot.domains
#print NJZ_PoolRoot.parent_clauses
#print axioms NJZ_PoolRoot.parent_clauses
#print NJZ_Weights.finish_source
#print axioms NJZ_Weights.finish_source
#print NJZ_Weights.value_source
#print axioms NJZ_Weights.value_source
#print NJJ_Value.projection
#print axioms NJJ_Value.projection
#print NJZ_Readers.e_reference
#print axioms NJZ_Readers.e_reference
#print NJZ_Readers.e_source
#print axioms NJZ_Readers.e_source
#print NJZ_Readers.e_window
#print axioms NJZ_Readers.e_window
#print NJZ_Readers.k_reference
#print axioms NJZ_Readers.k_reference
#print NJZ_Readers.k_source
#print axioms NJZ_Readers.k_source
#print NJZ_Readers.k_window
#print axioms NJZ_Readers.k_window
#print NJZ_Readers.raw
#print axioms NJZ_Readers.raw
#print NJZ_Readers.raw_cut
#print axioms NJZ_Readers.raw_cut
#print NJZ_CheckpointReaders.semantic
#print axioms NJZ_CheckpointReaders.semantic
#print NJZ_CheckpointReaders.scalar
#print axioms NJZ_CheckpointReaders.scalar
#print NJZ_CheckpointReaders.weights
#print axioms NJZ_CheckpointReaders.weights
#print NJR_WeightFailure.weights
#print axioms NJR_WeightFailure.weights
#print NJZ_Validator.source
#print axioms NJZ_Validator.source
#print NJZ_Validator.members
#print axioms NJZ_Validator.members
#print NJZ_Validator.unique
#print axioms NJZ_Validator.unique
#print AspisR1.NKD_Add.root
#print axioms AspisR1.NKD_Add.root
#print AspisR1.NKD_Decode.root
#print axioms AspisR1.NKD_Decode.root
#print AspisR1.NKD_Gamma.root
#print axioms AspisR1.NKD_Gamma.root
#print AspisR1.NKD_Values.gamma
#print axioms AspisR1.NKD_Values.gamma
#print AspisR1.NKD_Low.root
#print axioms AspisR1.NKD_Low.root
#print AspisR1.NKD_Ordinary.root
#print axioms AspisR1.NKD_Ordinary.root
#print AspisR1.NKD_Runtime.absorb_root
#print axioms AspisR1.NKD_Runtime.absorb_root
#print AspisR1.NKD_TranscriptPackets.absorb
#print axioms AspisR1.NKD_TranscriptPackets.absorb
#print AspisR1.NKD_Runtime.block_root
#print axioms AspisR1.NKD_Runtime.block_root
#print AspisR1.NKD_TranscriptPackets.block
#print axioms AspisR1.NKD_TranscriptPackets.block
#print AspisR1.NKD_Runtime.new_root
#print axioms AspisR1.NKD_Runtime.new_root
#print AspisR1.NKD_TranscriptPackets.new
#print axioms AspisR1.NKD_TranscriptPackets.new
#print AspisR1.NJX_PatternRoot.source
#print axioms AspisR1.NJX_PatternRoot.source
#print AspisR1.NJX_PatternForward.source
#print axioms AspisR1.NJX_PatternForward.source
#print AspisR1.NJX_LeftCutRoot.source
#print axioms AspisR1.NJX_LeftCutRoot.source
#print AspisR1.NJX_CarryRoot.source
#print axioms AspisR1.NJX_CarryRoot.source
#print AspisR1.NJX_RecipientRoot.source
#print axioms AspisR1.NJX_RecipientRoot.source
#print AspisR1.NJU_GeneralFinishRoot.finish
#print axioms AspisR1.NJU_GeneralFinishRoot.finish
#print AspisR1.NJU_GeneralFinishRoot.ported
#print axioms AspisR1.NJU_GeneralFinishRoot.ported
#print NJU_FinishAtCurrent.source_view
#print axioms NJU_FinishAtCurrent.source_view
#print NJU_CurrentWindows.rejects
#print axioms NJU_CurrentWindows.rejects
#print AspisR1.NJU_FinishInput.Holds
#print NJU_CurrentWindows.Holds
#print NJZ_CodecSemantics.Cut
#print NJZ_CodecSemantics.NativeCut
#print NJZ_CodecSemantics.ReplyDomain
#print NJZ_Readers.RawCut
#print AspisR1.NKD_Runtime.backend
run_cmd do
  let env ← getEnv
  for root in #["NJJ_Value.projection", "NJR_WeightFailure.weights"] do
    let name := root.toName
    let some c := env.find? name | throwError "missing root {root}"
    let some idx := env.getModuleIdxFor? name | throwError "missing owner {root}"
    let statement ← liftTermElabM (PrettyPrinter.ppExpr c.type)
    let row := Json.mkObj [("root",toJson root),("owner_module",toJson env.header.moduleNames[idx]!.toString),("obligation_statement",toJson statement.pretty)]
    logInfo m!"NKH_OWNER {row.compress}"
run_cmd do
  let env ← getEnv
  let mut seen : Std.HashSet Name := {}
  for idx in [:env.header.moduleNames.size] do
    let sourceModule := env.header.moduleNames[idx]!
    for declared in env.header.moduleData[idx]!.constants do
      let root := declared.name.toString
      if ((root.splitOn "JFw_Validator").length > 1 ∨ (root.splitOn "JFw_Record").length > 1) ∧
          (root.splitOn "match_").length > 1 then
        let some owner := env.getModuleIdxFor? declared.name | throwError "missing matcher owner {root}"
        let ownerModule := env.header.moduleNames[owner]!.toString
        unless ownerModule == "JFw_Validator" || ownerModule == "JFw_Record" do
          throwError "unexpected matcher owner {root}: {ownerModule}"
        unless seen.contains declared.name do
          seen := seen.insert declared.name
          logInfo m!"NKH_MATCHER_OWNER {(Json.mkObj [("root",toJson root),("owner_module",toJson ownerModule),("selected_table",toJson sourceModule.toString)]).compress}"
