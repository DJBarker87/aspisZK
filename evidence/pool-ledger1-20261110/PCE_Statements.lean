import Lean
import PCE_COMBINED_IMPORT
open Lean Elab Command
#check AspisR1.RPx_Deployed.deployed
run_cmd do
 let c ← Lean.getConstInfo `AspisR1.RPx_Deployed.deployed
 logInfo (Json.mkObj [("root",toJson "AspisR1.RPx_Deployed.deployed"),("type_expr",toJson (reprStr c.type)),("levels",toJson (c.levelParams.map Name.toString))]).compress
#check PCB_Location.result
run_cmd do
 let c ← Lean.getConstInfo `PCB_Location.result
 logInfo (Json.mkObj [("root",toJson "PCB_Location.result"),("type_expr",toJson (reprStr c.type)),("levels",toJson (c.levelParams.map Name.toString))]).compress
#check NHC_NGG_Loader.result
run_cmd do
 let c ← Lean.getConstInfo `NHC_NGG_Loader.result
 logInfo (Json.mkObj [("root",toJson "NHC_NGG_Loader.result"),("type_expr",toJson (reprStr c.type)),("levels",toJson (c.levelParams.map Name.toString))]).compress
#check NHC_ErrorConversion.result
run_cmd do
 let c ← Lean.getConstInfo `NHC_ErrorConversion.result
 logInfo (Json.mkObj [("root",toJson "NHC_ErrorConversion.result"),("type_expr",toJson (reprStr c.type)),("levels",toJson (c.levelParams.map Name.toString))]).compress
#check NHP_ConstructorPackets.exact_arms
run_cmd do
 let c ← Lean.getConstInfo `NHP_ConstructorPackets.exact_arms
 logInfo (Json.mkObj [("root",toJson "NHP_ConstructorPackets.exact_arms"),("type_expr",toJson (reprStr c.type)),("levels",toJson (c.levelParams.map Name.toString))]).compress
#check PCB_SmallStatementLaws.sentinel
run_cmd do
 let c ← Lean.getConstInfo `PCB_SmallStatementLaws.sentinel
 logInfo (Json.mkObj [("root",toJson "PCB_SmallStatementLaws.sentinel"),("type_expr",toJson (reprStr c.type)),("levels",toJson (c.levelParams.map Name.toString))]).compress
#check PCB_SmallStatementLaws.full
run_cmd do
 let c ← Lean.getConstInfo `PCB_SmallStatementLaws.full
 logInfo (Json.mkObj [("root",toJson "PCB_SmallStatementLaws.full"),("type_expr",toJson (reprStr c.type)),("levels",toJson (c.levelParams.map Name.toString))]).compress
#check PCB_ErrorLaws.receipt
run_cmd do
 let c ← Lean.getConstInfo `PCB_ErrorLaws.receipt
 logInfo (Json.mkObj [("root",toJson "PCB_ErrorLaws.receipt"),("type_expr",toJson (reprStr c.type)),("levels",toJson (c.levelParams.map Name.toString))]).compress
#check PCB_ErrorLaws.account
run_cmd do
 let c ← Lean.getConstInfo `PCB_ErrorLaws.account
 logInfo (Json.mkObj [("root",toJson "PCB_ErrorLaws.account"),("type_expr",toJson (reprStr c.type)),("levels",toJson (c.levelParams.map Name.toString))]).compress
#check PCB_ErrorLaws.forest
run_cmd do
 let c ← Lean.getConstInfo `PCB_ErrorLaws.forest
 logInfo (Json.mkObj [("root",toJson "PCB_ErrorLaws.forest"),("type_expr",toJson (reprStr c.type)),("levels",toJson (c.levelParams.map Name.toString))]).compress
#check PCB_VaultLaw.result
run_cmd do
 let c ← Lean.getConstInfo `PCB_VaultLaw.result
 logInfo (Json.mkObj [("root",toJson "PCB_VaultLaw.result"),("type_expr",toJson (reprStr c.type)),("levels",toJson (c.levelParams.map Name.toString))]).compress
#check PCB_AppendFrame.geometry
run_cmd do
 let c ← Lean.getConstInfo `PCB_AppendFrame.geometry
 logInfo (Json.mkObj [("root",toJson "PCB_AppendFrame.geometry"),("type_expr",toJson (reprStr c.type)),("levels",toJson (c.levelParams.map Name.toString))]).compress
#check PCB_AppendFrame.step_byte
run_cmd do
 let c ← Lean.getConstInfo `PCB_AppendFrame.step_byte
 logInfo (Json.mkObj [("root",toJson "PCB_AppendFrame.step_byte"),("type_expr",toJson (reprStr c.type)),("levels",toJson (c.levelParams.map Name.toString))]).compress
#check PCB_AppendFrame.step_frame
run_cmd do
 let c ← Lean.getConstInfo `PCB_AppendFrame.step_frame
 logInfo (Json.mkObj [("root",toJson "PCB_AppendFrame.step_frame"),("type_expr",toJson (reprStr c.type)),("levels",toJson (c.levelParams.map Name.toString))]).compress
#check PCB_AppendFrame.retained
run_cmd do
 let c ← Lean.getConstInfo `PCB_AppendFrame.retained
 logInfo (Json.mkObj [("root",toJson "PCB_AppendFrame.retained"),("type_expr",toJson (reprStr c.type)),("levels",toJson (c.levelParams.map Name.toString))]).compress
#check PCB_AppendFrame.run_frame
run_cmd do
 let c ← Lean.getConstInfo `PCB_AppendFrame.run_frame
 logInfo (Json.mkObj [("root",toJson "PCB_AppendFrame.run_frame"),("type_expr",toJson (reprStr c.type)),("levels",toJson (c.levelParams.map Name.toString))]).compress
#check PCB_AppendFrame.finish_roots
run_cmd do
 let c ← Lean.getConstInfo `PCB_AppendFrame.finish_roots
 logInfo (Json.mkObj [("root",toJson "PCB_AppendFrame.finish_roots"),("type_expr",toJson (reprStr c.type)),("levels",toJson (c.levelParams.map Name.toString))]).compress
#check PCB_AppendFrame.complete_retained
run_cmd do
 let c ← Lean.getConstInfo `PCB_AppendFrame.complete_retained
 logInfo (Json.mkObj [("root",toJson "PCB_AppendFrame.complete_retained"),("type_expr",toJson (reprStr c.type)),("levels",toJson (c.levelParams.map Name.toString))]).compress
#check PCB_GetterLaws.tree
run_cmd do
 let c ← Lean.getConstInfo `PCB_GetterLaws.tree
 logInfo (Json.mkObj [("root",toJson "PCB_GetterLaws.tree"),("type_expr",toJson (reprStr c.type)),("levels",toJson (c.levelParams.map Name.toString))]).compress
#check PCB_GetterLaws.deref_tree
run_cmd do
 let c ← Lean.getConstInfo `PCB_GetterLaws.deref_tree
 logInfo (Json.mkObj [("root",toJson "PCB_GetterLaws.deref_tree"),("type_expr",toJson (reprStr c.type)),("levels",toJson (c.levelParams.map Name.toString))]).compress
#check PCB_GetterLaws.seed
run_cmd do
 let c ← Lean.getConstInfo `PCB_GetterLaws.seed
 logInfo (Json.mkObj [("root",toJson "PCB_GetterLaws.seed"),("type_expr",toJson (reprStr c.type)),("levels",toJson (c.levelParams.map Name.toString))]).compress
#check PCB_GetterLaws.value
run_cmd do
 let c ← Lean.getConstInfo `PCB_GetterLaws.value
 logInfo (Json.mkObj [("root",toJson "PCB_GetterLaws.value"),("type_expr",toJson (reprStr c.type)),("levels",toJson (c.levelParams.map Name.toString))]).compress
#check PCB_GetterLaws.state
run_cmd do
 let c ← Lean.getConstInfo `PCB_GetterLaws.state
 logInfo (Json.mkObj [("root",toJson "PCB_GetterLaws.state"),("type_expr",toJson (reprStr c.type)),("levels",toJson (c.levelParams.map Name.toString))]).compress
#check PCB_RegistryLaws.selection
run_cmd do
 let c ← Lean.getConstInfo `PCB_RegistryLaws.selection
 logInfo (Json.mkObj [("root",toJson "PCB_RegistryLaws.selection"),("type_expr",toJson (reprStr c.type)),("levels",toJson (c.levelParams.map Name.toString))]).compress
#check PCB_RegistryLaws.owner
run_cmd do
 let c ← Lean.getConstInfo `PCB_RegistryLaws.owner
 logInfo (Json.mkObj [("root",toJson "PCB_RegistryLaws.owner"),("type_expr",toJson (reprStr c.type)),("levels",toJson (c.levelParams.map Name.toString))]).compress
#check PCB_FinalLaws.clear
run_cmd do
 let c ← Lean.getConstInfo `PCB_FinalLaws.clear
 logInfo (Json.mkObj [("root",toJson "PCB_FinalLaws.clear"),("type_expr",toJson (reprStr c.type)),("levels",toJson (c.levelParams.map Name.toString))]).compress
#check PCB_FinalLaws.preparation
run_cmd do
 let c ← Lean.getConstInfo `PCB_FinalLaws.preparation
 logInfo (Json.mkObj [("root",toJson "PCB_FinalLaws.preparation"),("type_expr",toJson (reprStr c.type)),("levels",toJson (c.levelParams.map Name.toString))]).compress
#check PCB_AppendScalarLaws.geometry
run_cmd do
 let c ← Lean.getConstInfo `PCB_AppendScalarLaws.geometry
 logInfo (Json.mkObj [("root",toJson "PCB_AppendScalarLaws.geometry"),("type_expr",toJson (reprStr c.type)),("levels",toJson (c.levelParams.map Name.toString))]).compress
#check PCB_AppendScalarLaws.filled
run_cmd do
 let c ← Lean.getConstInfo `PCB_AppendScalarLaws.filled
 logInfo (Json.mkObj [("root",toJson "PCB_AppendScalarLaws.filled"),("type_expr",toJson (reprStr c.type)),("levels",toJson (c.levelParams.map Name.toString))]).compress
#check PCA.PCA_Owner.spec
run_cmd do
 let c ← Lean.getConstInfo `PCA.PCA_Owner.spec
 logInfo (Json.mkObj [("root",toJson "PCA.PCA_Owner.spec"),("type_expr",toJson (reprStr c.type)),("levels",toJson (c.levelParams.map Name.toString))]).compress
#check PCA.Borrow.acquire_preserves
run_cmd do
 let c ← Lean.getConstInfo `PCA.Borrow.acquire_preserves
 logInfo (Json.mkObj [("root",toJson "PCA.Borrow.acquire_preserves"),("type_expr",toJson (reprStr c.type)),("levels",toJson (c.levelParams.map Name.toString))]).compress
#check PCA.Borrow.read_preserves
run_cmd do
 let c ← Lean.getConstInfo `PCA.Borrow.read_preserves
 logInfo (Json.mkObj [("root",toJson "PCA.Borrow.read_preserves"),("type_expr",toJson (reprStr c.type)),("levels",toJson (c.levelParams.map Name.toString))]).compress
#check PCA.Borrow.copy_preserves
run_cmd do
 let c ← Lean.getConstInfo `PCA.Borrow.copy_preserves
 logInfo (Json.mkObj [("root",toJson "PCA.Borrow.copy_preserves"),("type_expr",toJson (reprStr c.type)),("levels",toJson (c.levelParams.map Name.toString))]).compress
#check PCA.Borrow.cleanup_preserves
run_cmd do
 let c ← Lean.getConstInfo `PCA.Borrow.cleanup_preserves
 logInfo (Json.mkObj [("root",toJson "PCA.Borrow.cleanup_preserves"),("type_expr",toJson (reprStr c.type)),("levels",toJson (c.levelParams.map Name.toString))]).compress
#check PCA.Borrow.finish_preserves
run_cmd do
 let c ← Lean.getConstInfo `PCA.Borrow.finish_preserves
 logInfo (Json.mkObj [("root",toJson "PCA.Borrow.finish_preserves"),("type_expr",toJson (reprStr c.type)),("levels",toJson (c.levelParams.map Name.toString))]).compress
#check PCA.protected_view
run_cmd do
 let c ← Lean.getConstInfo `PCA.protected_view
 logInfo (Json.mkObj [("root",toJson "PCA.protected_view"),("type_expr",toJson (reprStr c.type)),("levels",toJson (c.levelParams.map Name.toString))]).compress
#check PCA.changed_unpassed_excludes_candidate
run_cmd do
 let c ← Lean.getConstInfo `PCA.changed_unpassed_excludes_candidate
 logInfo (Json.mkObj [("root",toJson "PCA.changed_unpassed_excludes_candidate"),("type_expr",toJson (reprStr c.type)),("levels",toJson (c.levelParams.map Name.toString))]).compress
#check PCA.exclusive_release_result
run_cmd do
 let c ← Lean.getConstInfo `PCA.exclusive_release_result
 logInfo (Json.mkObj [("root",toJson "PCA.exclusive_release_result"),("type_expr",toJson (reprStr c.type)),("levels",toJson (c.levelParams.map Name.toString))]).compress
#check PCA.exclusive_release_zero
run_cmd do
 let c ← Lean.getConstInfo `PCA.exclusive_release_zero
 logInfo (Json.mkObj [("root",toJson "PCA.exclusive_release_zero"),("type_expr",toJson (reprStr c.type)),("levels",toJson (c.levelParams.map Name.toString))]).compress
#check PCA.cleanup_two_order
run_cmd do
 let c ← Lean.getConstInfo `PCA.cleanup_two_order
 logInfo (Json.mkObj [("root",toJson "PCA.cleanup_two_order"),("type_expr",toJson (reprStr c.type)),("levels",toJson (c.levelParams.map Name.toString))]).compress
#check PCA.abort_keeps_loans
run_cmd do
 let c ← Lean.getConstInfo `PCA.abort_keeps_loans
 logInfo (Json.mkObj [("root",toJson "PCA.abort_keeps_loans"),("type_expr",toJson (reprStr c.type)),("levels",toJson (c.levelParams.map Name.toString))]).compress
#check PCA.count_ok
run_cmd do
 let c ← Lean.getConstInfo `PCA.count_ok
 logInfo (Json.mkObj [("root",toJson "PCA.count_ok"),("type_expr",toJson (reprStr c.type)),("levels",toJson (c.levelParams.map Name.toString))]).compress
#check PCA.count_frame
run_cmd do
 let c ← Lean.getConstInfo `PCA.count_frame
 logInfo (Json.mkObj [("root",toJson "PCA.count_frame"),("type_expr",toJson (reprStr c.type)),("levels",toJson (c.levelParams.map Name.toString))]).compress
#check PCA.held_excluded
run_cmd do
 let c ← Lean.getConstInfo `PCA.held_excluded
 logInfo (Json.mkObj [("root",toJson "PCA.held_excluded"),("type_expr",toJson (reprStr c.type)),("levels",toJson (c.levelParams.map Name.toString))]).compress
#check PCA.RowSpec_POOL_165
run_cmd do
 let c ← Lean.getConstInfo `PCA.RowSpec_POOL_165
 logInfo (Json.mkObj [("root",toJson "PCA.RowSpec_POOL_165"),("type_expr",toJson (reprStr c.type)),("levels",toJson (c.levelParams.map Name.toString))]).compress
#check PCA.RowSpec_POOL_199
run_cmd do
 let c ← Lean.getConstInfo `PCA.RowSpec_POOL_199
 logInfo (Json.mkObj [("root",toJson "PCA.RowSpec_POOL_199"),("type_expr",toJson (reprStr c.type)),("levels",toJson (c.levelParams.map Name.toString))]).compress
#check PCA.RowSpec_POOL_220
run_cmd do
 let c ← Lean.getConstInfo `PCA.RowSpec_POOL_220
 logInfo (Json.mkObj [("root",toJson "PCA.RowSpec_POOL_220"),("type_expr",toJson (reprStr c.type)),("levels",toJson (c.levelParams.map Name.toString))]).compress
#check PCA.RowSpec_POOL_222
run_cmd do
 let c ← Lean.getConstInfo `PCA.RowSpec_POOL_222
 logInfo (Json.mkObj [("root",toJson "PCA.RowSpec_POOL_222"),("type_expr",toJson (reprStr c.type)),("levels",toJson (c.levelParams.map Name.toString))]).compress
#check PCA.RowSpec_POOL_246
run_cmd do
 let c ← Lean.getConstInfo `PCA.RowSpec_POOL_246
 logInfo (Json.mkObj [("root",toJson "PCA.RowSpec_POOL_246"),("type_expr",toJson (reprStr c.type)),("levels",toJson (c.levelParams.map Name.toString))]).compress
#check PCA.RowSpec_POOL_279
run_cmd do
 let c ← Lean.getConstInfo `PCA.RowSpec_POOL_279
 logInfo (Json.mkObj [("root",toJson "PCA.RowSpec_POOL_279"),("type_expr",toJson (reprStr c.type)),("levels",toJson (c.levelParams.map Name.toString))]).compress
#check PCA.RowSpec_POOL_280
run_cmd do
 let c ← Lean.getConstInfo `PCA.RowSpec_POOL_280
 logInfo (Json.mkObj [("root",toJson "PCA.RowSpec_POOL_280"),("type_expr",toJson (reprStr c.type)),("levels",toJson (c.levelParams.map Name.toString))]).compress
#check PCA.RowSpec_POOL_286
run_cmd do
 let c ← Lean.getConstInfo `PCA.RowSpec_POOL_286
 logInfo (Json.mkObj [("root",toJson "PCA.RowSpec_POOL_286"),("type_expr",toJson (reprStr c.type)),("levels",toJson (c.levelParams.map Name.toString))]).compress
#check PCA.RowSpec_POOL_301
run_cmd do
 let c ← Lean.getConstInfo `PCA.RowSpec_POOL_301
 logInfo (Json.mkObj [("root",toJson "PCA.RowSpec_POOL_301"),("type_expr",toJson (reprStr c.type)),("levels",toJson (c.levelParams.map Name.toString))]).compress
#check PCA.RowSpec_POOL_304
run_cmd do
 let c ← Lean.getConstInfo `PCA.RowSpec_POOL_304
 logInfo (Json.mkObj [("root",toJson "PCA.RowSpec_POOL_304"),("type_expr",toJson (reprStr c.type)),("levels",toJson (c.levelParams.map Name.toString))]).compress
#check PCA.RowSpec_POOL_309
run_cmd do
 let c ← Lean.getConstInfo `PCA.RowSpec_POOL_309
 logInfo (Json.mkObj [("root",toJson "PCA.RowSpec_POOL_309"),("type_expr",toJson (reprStr c.type)),("levels",toJson (c.levelParams.map Name.toString))]).compress
#check PCA.RowSpec_POOL_313
run_cmd do
 let c ← Lean.getConstInfo `PCA.RowSpec_POOL_313
 logInfo (Json.mkObj [("root",toJson "PCA.RowSpec_POOL_313"),("type_expr",toJson (reprStr c.type)),("levels",toJson (c.levelParams.map Name.toString))]).compress
#check PCA.RowSpec_POOL_326
run_cmd do
 let c ← Lean.getConstInfo `PCA.RowSpec_POOL_326
 logInfo (Json.mkObj [("root",toJson "PCA.RowSpec_POOL_326"),("type_expr",toJson (reprStr c.type)),("levels",toJson (c.levelParams.map Name.toString))]).compress
#check PCA.RowSpec_POOL_332
run_cmd do
 let c ← Lean.getConstInfo `PCA.RowSpec_POOL_332
 logInfo (Json.mkObj [("root",toJson "PCA.RowSpec_POOL_332"),("type_expr",toJson (reprStr c.type)),("levels",toJson (c.levelParams.map Name.toString))]).compress
#check PCA.RowSpec_POOL_333
run_cmd do
 let c ← Lean.getConstInfo `PCA.RowSpec_POOL_333
 logInfo (Json.mkObj [("root",toJson "PCA.RowSpec_POOL_333"),("type_expr",toJson (reprStr c.type)),("levels",toJson (c.levelParams.map Name.toString))]).compress
#check PCA.RowSpec_POOL_340
run_cmd do
 let c ← Lean.getConstInfo `PCA.RowSpec_POOL_340
 logInfo (Json.mkObj [("root",toJson "PCA.RowSpec_POOL_340"),("type_expr",toJson (reprStr c.type)),("levels",toJson (c.levelParams.map Name.toString))]).compress
#check PCA.RowSpec_POOL_358
run_cmd do
 let c ← Lean.getConstInfo `PCA.RowSpec_POOL_358
 logInfo (Json.mkObj [("root",toJson "PCA.RowSpec_POOL_358"),("type_expr",toJson (reprStr c.type)),("levels",toJson (c.levelParams.map Name.toString))]).compress
#check PCA.RowSpec_POOL_362
run_cmd do
 let c ← Lean.getConstInfo `PCA.RowSpec_POOL_362
 logInfo (Json.mkObj [("root",toJson "PCA.RowSpec_POOL_362"),("type_expr",toJson (reprStr c.type)),("levels",toJson (c.levelParams.map Name.toString))]).compress
#check PCA.RowSpec_POOL_364
run_cmd do
 let c ← Lean.getConstInfo `PCA.RowSpec_POOL_364
 logInfo (Json.mkObj [("root",toJson "PCA.RowSpec_POOL_364"),("type_expr",toJson (reprStr c.type)),("levels",toJson (c.levelParams.map Name.toString))]).compress
#check PCA.RowSpec_POOL_365
run_cmd do
 let c ← Lean.getConstInfo `PCA.RowSpec_POOL_365
 logInfo (Json.mkObj [("root",toJson "PCA.RowSpec_POOL_365"),("type_expr",toJson (reprStr c.type)),("levels",toJson (c.levelParams.map Name.toString))]).compress
#check PCA.RowSpec_POOL_367
run_cmd do
 let c ← Lean.getConstInfo `PCA.RowSpec_POOL_367
 logInfo (Json.mkObj [("root",toJson "PCA.RowSpec_POOL_367"),("type_expr",toJson (reprStr c.type)),("levels",toJson (c.levelParams.map Name.toString))]).compress
#check PCA.RowSpec_POOL_382
run_cmd do
 let c ← Lean.getConstInfo `PCA.RowSpec_POOL_382
 logInfo (Json.mkObj [("root",toJson "PCA.RowSpec_POOL_382"),("type_expr",toJson (reprStr c.type)),("levels",toJson (c.levelParams.map Name.toString))]).compress
#check PCA.RowSpec_POOL_388
run_cmd do
 let c ← Lean.getConstInfo `PCA.RowSpec_POOL_388
 logInfo (Json.mkObj [("root",toJson "PCA.RowSpec_POOL_388"),("type_expr",toJson (reprStr c.type)),("levels",toJson (c.levelParams.map Name.toString))]).compress
#check PCA.RowSpec_POOL_395
run_cmd do
 let c ← Lean.getConstInfo `PCA.RowSpec_POOL_395
 logInfo (Json.mkObj [("root",toJson "PCA.RowSpec_POOL_395"),("type_expr",toJson (reprStr c.type)),("levels",toJson (c.levelParams.map Name.toString))]).compress
#check PCA.Transcription.pure_preserves
run_cmd do
 let c ← Lean.getConstInfo `PCA.Transcription.pure_preserves
 logInfo (Json.mkObj [("root",toJson "PCA.Transcription.pure_preserves"),("type_expr",toJson (reprStr c.type)),("levels",toJson (c.levelParams.map Name.toString))]).compress
#check PCA.Transcription.bind_preserves
run_cmd do
 let c ← Lean.getConstInfo `PCA.Transcription.bind_preserves
 logInfo (Json.mkObj [("root",toJson "PCA.Transcription.bind_preserves"),("type_expr",toJson (reprStr c.type)),("levels",toJson (c.levelParams.map Name.toString))]).compress
#check PCA.Transcription.call_preserves
run_cmd do
 let c ← Lean.getConstInfo `PCA.Transcription.call_preserves
 logInfo (Json.mkObj [("root",toJson "PCA.Transcription.call_preserves"),("type_expr",toJson (reprStr c.type)),("levels",toJson (c.levelParams.map Name.toString))]).compress
#check PCA.Transcription.get_preserves
run_cmd do
 let c ← Lean.getConstInfo `PCA.Transcription.get_preserves
 logInfo (Json.mkObj [("root",toJson "PCA.Transcription.get_preserves"),("type_expr",toJson (reprStr c.type)),("levels",toJson (c.levelParams.map Name.toString))]).compress
#check PCA.Transcription.check_preserves
run_cmd do
 let c ← Lean.getConstInfo `PCA.Transcription.check_preserves
 logInfo (Json.mkObj [("root",toJson "PCA.Transcription.check_preserves"),("type_expr",toJson (reprStr c.type)),("levels",toJson (c.levelParams.map Name.toString))]).compress
#check PCA.Transcription.branch_preserves
run_cmd do
 let c ← Lean.getConstInfo `PCA.Transcription.branch_preserves
 logInfo (Json.mkObj [("root",toJson "PCA.Transcription.branch_preserves"),("type_expr",toJson (reprStr c.type)),("levels",toJson (c.levelParams.map Name.toString))]).compress
#check PCA.Transcription.account_preserves
run_cmd do
 let c ← Lean.getConstInfo `PCA.Transcription.account_preserves
 logInfo (Json.mkObj [("root",toJson "PCA.Transcription.account_preserves"),("type_expr",toJson (reprStr c.type)),("levels",toJson (c.levelParams.map Name.toString))]).compress
