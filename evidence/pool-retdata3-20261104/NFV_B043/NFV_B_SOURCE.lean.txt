import NFV_Accounts
import NFV_HelperModel
import NFV_RequestGuards
/-!
Account list value laws are proved in NFV_Accounts. The inherited model join
and helper semantics below remain distinct from production native transport.
No theorem asserting the OPEN production prefix association is introduced.
-/
#print axioms NFV_Accounts.keys
#print axioms NFV_Accounts.flags
#print axioms NFV_Accounts.account_order
#print axioms NFR_ModelJoin.same_emitted_settlement
#print axioms NFR_CHelperBridge.semantic
#print axioms NFR_CHelperBridge.same_emission

#print axioms NFV_HelperModel.erase
#print axioms NFV_HelperModel.same_emission

#print axioms NFV_Copy.range
#print axioms NFV_Copy.prefix_copy
#print axioms NFV_Copy.suffix
#print axioms NFV_Copy.update
#print axioms NFV_Copy.bind_pair_finish
#print axioms NFV_Copy.range_then
#print axioms NFV_Copy.prefix_then
#print axioms NFV_Copy.suffix_then
#print axioms NFV_ListFrames.set_next
#print axioms NFV_ListFrames.copy_next
#print axioms NFV_ListFrames.copy_at
#print axioms NFV_Envelope.emitted
#print axioms NFV_Envelope.header_value
#print axioms NFV_Envelope.pure_value
#print axioms NFV_RequestWindows.complete
#print axioms NFV_RequestWindows.envelope
#print axioms NFV_RequestOracle.erase
#print axioms NFV_RequestOracle.profile_rejected

#print axioms NFV_RequestIndexes.window
#print axioms NFV_RequestIndexes.header
#print axioms NFV_RequestIndexes.profile
#print axioms NFV_RequestIndexes.release
#print axioms NFV_RequestIndexes.program
#print axioms NFV_RequestIndexes.payment

#print axioms NFV_RequestGuards.lists
#print axioms NFV_RequestGuards.array
#print axioms NFV_RequestGuards.zero_binding
