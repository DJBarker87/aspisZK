import Lean
import NGK_NFV_Accounts
import NGK_NFV_HelperModel
import NGK_NFV_RequestGuards

/-!
Account list value laws are proved in NGK_NFV_Accounts. The inherited model join
and helper semantics below remain distinct from production native transport.
No theorem asserting the OPEN production prefix association is introduced.
-/
#print axioms NGK_NFV_Accounts.keys
#print axioms NGK_NFV_Accounts.flags
#print axioms NGK_NFV_Accounts.account_order
#print axioms NGK_NFR_ModelJoin.same_emitted_settlement
#print axioms NGK_NFR_CHelperBridge.semantic
#print axioms NGK_NFR_CHelperBridge.same_emission

#print axioms NGK_NFV_HelperModel.erase
#print axioms NGK_NFV_HelperModel.same_emission

#print axioms NGK_NFV_Copy.range
#print axioms NGK_NFV_Copy.prefix_copy
#print axioms NGK_NFV_Copy.suffix
#print axioms NGK_NFV_Copy.update
#print axioms NGK_NFV_Copy.bind_pair_finish
#print axioms NGK_NFV_Copy.range_then
#print axioms NGK_NFV_Copy.prefix_then
#print axioms NGK_NFV_Copy.suffix_then
#print axioms NGK_NFV_ListFrames.set_next
#print axioms NGK_NFV_ListFrames.copy_next
#print axioms NGK_NFV_ListFrames.copy_at
#print axioms NGK_NFV_Envelope.emitted
#print axioms NGK_NFV_Envelope.header_value
#print axioms NGK_NFV_Envelope.pure_value
#print axioms NGK_NFV_RequestWindows.complete
#print axioms NGK_NFV_RequestWindows.envelope
#print axioms NGK_NFV_RequestOracle.erase
#print axioms NGK_NFV_RequestOracle.profile_rejected

#print axioms NGK_NFV_RequestIndexes.window
#print axioms NGK_NFV_RequestIndexes.header
#print axioms NGK_NFV_RequestIndexes.profile
#print axioms NGK_NFV_RequestIndexes.release
#print axioms NGK_NFV_RequestIndexes.program
#print axioms NGK_NFV_RequestIndexes.payment

#print axioms NGK_NFV_RequestGuards.lists
#print axioms NGK_NFV_RequestGuards.array
#print axioms NGK_NFV_RequestGuards.zero_binding

run_cmd do
 let env ← Lean.getEnv
 env.constants.toList.forM fun (n, ci) => do
  if ci.isTheorem && (env.getModuleIdxFor? n).isNone then
   Lean.Elab.Command.elabCommand (← `(command| #print axioms $(Lean.mkIdent n)))
