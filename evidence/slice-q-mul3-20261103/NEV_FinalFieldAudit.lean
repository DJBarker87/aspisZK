import NEV_ReachedProgress
-- Import repair prepared after budget exhaustion; NOT REPLAYED.
import NEV_PrefixPacket
import NEV_AccumPacket
import NEV_QRawAssociation
import NEV_DotPush
import NEV_EbyPushAssociation
import NEV_DotFoldInvariant

#print axioms NEV_PrefixPacket.result_state_effects
#print axioms NEV_AccumPacket.raw_length
#print axioms NEV_AccumPacket.result_state_effects
#print axioms NEV_AccumPacket.no_base_dependency
#print axioms NEV_ReachedProgress.next
#print axioms NEV_QRawAssociation.actual
#print axioms NEV_QRawAssociation.cohort
#print axioms NEV_DotPush.association
#print axioms NEV_DotPush.complete
#print axioms NEV_EbyPushAssociation.source
#print axioms NEV_DotScalar.product
#print axioms NEV_DotFoldInvariant.total
#print axioms NEV_DotFoldInvariant.native_domain
