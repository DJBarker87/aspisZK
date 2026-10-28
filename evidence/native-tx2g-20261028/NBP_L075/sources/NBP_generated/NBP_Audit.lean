import NBG_Audit
import NBP_ArrayIndex
import NBP_BindPair
import NBP_CommonBytes
import NBP_CommonDecode
import NBP_CommonTail0
import NBP_CommonTail1
import NBP_CommonTail2
import NBP_CommonTail3
import NBP_CommonTail4
import NBP_CommonTail5
import NBP_CommonTail6
import NBP_Decode1
import NBP_Decode2
import NBP_Decode3
import NBP_Decode4
import NBP_Decode5
import NBP_Decode6
import NBP_Decode7
import NBP_DecodeSuccess
import NBP_DecodeWord
import NBP_DigestDecode
import NBP_DigestEncode
import NBP_DigestLayout
import NBP_ErrorLabels
import NBP_FilledPorts
import NBP_PaymentModel
import NBP_PrefixStore
import NBP_Read
import NBP_Store
import NBP_TransferDecode
import NBP_TransferEncode
import NBP_WithdrawalDecode
import NBP_WithdrawalEncode
set_option autoImplicit false
#print axioms NBP_ArrayIndex.index_mut
#print axioms NBP_ArrayIndex.copy
#print axioms NBP_ArrayIndex.slice_length
#print axioms NBP_ArrayIndex.copy_range
#print axioms NBP_ArrayIndex.prefix_index
#print axioms NBP_ArrayIndex.suffix_index
#print axioms NBP_BindPair.pair
#print axioms NBP_BindPair.cases_bind
#print axioms NBP_CommonBytes.association
#print axioms NBP_CommonBytes.result
#print axioms NBP_CommonDecode.result
#print axioms NBP_CommonTail0.result
#print axioms NBP_CommonTail1.result
#print axioms NBP_CommonTail2.result
#print axioms NBP_CommonTail3.result
#print axioms NBP_CommonTail4.result
#print axioms NBP_CommonTail5.result
#print axioms NBP_CommonTail6.result
#print axioms NBP_Decode1.result
#print axioms NBP_Decode2.result
#print axioms NBP_Decode3.result
#print axioms NBP_Decode4.result
#print axioms NBP_Decode5.result
#print axioms NBP_Decode6.result
#print axioms NBP_Decode7.result
#print axioms NBP_DecodeSuccess.result
#print axioms NBP_DecodeWord.reject0
#print axioms NBP_DigestDecode.result
#print axioms NBP_DigestEncode.result
#print axioms NBP_DigestEncode.step
#print axioms NBP_DigestLayout.bytes
#print axioms NBP_ErrorLabels.labels
#print axioms NBP_FilledPorts.allocation
#print axioms NBP_FilledPorts.zero
#print axioms NBP_PrefixStore.store_then
#print axioms NBP_Read.copy
#print axioms NBP_Store.exact
#print axioms NBP_Store.store_then
#print axioms NBP_Store.update
#print axioms NBP_TransferDecode.fixed
#print axioms NBP_TransferDecode.result
#print axioms NBP_TransferEncode.result
#print axioms NBP_WithdrawalDecode.fixed
#print axioms NBP_WithdrawalDecode.result
#print axioms NBP_WithdrawalEncode.result
#print axioms NBC_Filled.result
#print axioms NBG_Error.transition
#print axioms AspisR1.S2K.DigestBytes.exact
#print axioms AspisR1.S2K.DigestBytes.loop_exact
#print axioms AspisR1.S2K.DigestTotal.next_row
#print axioms AspisR1.S2K.DigestTotal.body_word
#print axioms AspisR1.S2K.DigestTotal.exhausted
