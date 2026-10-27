import R1Z.PV_Inv_UniqueSlot
import R0P.CopyRegistry
set_option autoImplicit false
namespace R1Z.PV_Inv_RegistrySlot
open R0P
variable {K : Type} [Field K]
attribute [local irreducible] copyLinks copyPatterns copyActiveRowMasks copyInactiveRows

theorem producer (t : Trace K) (lambda : K) (link : CopyLink) (member : link ∈ copyLinks) :
    copyRowValues t lambda link.producer.row CopyLink.producer link.producer.slot =
      copyTupleValue lambda (copyEndpointTuple t link.tag link.producer) := by
  have h := PV_Inv_UniqueSlot.selected_eq copyLinks
    (fun l => (l.producer.row,l.producer.slot))
    (fun l => copyTupleValue lambda (copyEndpointTuple t l.tag l.producer))
    copy_producer_slots_nodup link member
  simpa only [PV_Inv_UniqueSlot.selectedSum,Prod.mk.injEq] using h

theorem consumer (t : Trace K) (lambda : K) (link : CopyLink) (member : link ∈ copyLinks) :
    copyRowValues t lambda link.consumer.row CopyLink.consumer link.consumer.slot =
      copyTupleValue lambda (copyEndpointTuple t link.tag link.consumer) := by
  have h := PV_Inv_UniqueSlot.selected_eq copyLinks
    (fun l => (l.consumer.row,l.consumer.slot))
    (fun l => copyTupleValue lambda (copyEndpointTuple t l.tag l.consumer))
    copy_consumer_slots_nodup link member
  simpa only [PV_Inv_UniqueSlot.selectedSum,Prod.mk.injEq] using h

#print axioms producer
#print axioms consumer
end R1Z.PV_Inv_RegistrySlot
