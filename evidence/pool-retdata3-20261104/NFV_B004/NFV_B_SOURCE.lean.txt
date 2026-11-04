import NFV_Accounts
import NFV_HelperModel
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
