import NGK_COMBINED_IMPORT
import NHR_tx2_common.Funs
import NHR_tx2_authenticated.Funs
import NHT_PacketAuth
import NHT_AuthCarriers
import NHT_AdapterInstall
import NHT_FinishPacket
import NHT_QueryTail
import NHT_PowersDomain
import NHT_Offsets
import NHI_Scalar
import NHI_Tensor
#check AspisR1.RPx_Deployed.deployed
#check NHT_Tx2CommonModel.source
#check NHT_Tx2AuthModel.source
#check NHT_PacketOps.source
#check NHT_PacketOps.query_source
#check NHT_QueryTail.source
#check NHT_FinishPacket.source
#check AspisR1.NHT_AuthCarriers.authenticated_saved_to_carriers
#check AspisR1.NGS_CARRIERS.same_inputs_or_collision
#check AspisR1.NGR_HISTORY.saved_to_loaded
#check NHI_Scalar.cohort
#check NHI_Tensor.cohort
#print axioms AspisR1.RPx_Deployed.deployed
#print axioms NHT_Tx2CommonModel.source
#print axioms NHT_Tx2AuthModel.source
#print axioms NHT_FinishPacket.source
#print axioms NHT_QueryTail.source
#print axioms AspisR1.NHT_AuthCarriers.authenticated_saved_to_carriers
