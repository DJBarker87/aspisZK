import PCD_Row320
import PCD_RequestRoot
import PCF_Payer
import PCF_Token
import PCG_AddressRoots
import PCI_Note
set_option autoImplicit false
#check PCD_Row320.result_state_effects
#check PCD_Row320.RowSpec_POOL_320
#check PCD_RequestRoot.result_state_effects
#check PCD_RequestRoot.emitted_reply
#check PCF_Payer.result_state_effects
#check PCF_Token.result_state_effects
#check PCI_Note.forwarding
#print axioms PCD_Row320.result_state_effects
#print axioms PCD_RequestRoot.result_state_effects
#print axioms PCF_Payer.result_state_effects
#print axioms PCF_Token.result_state_effects
#print axioms PCI_Note.forwarding
