import R1Z.PV_Inv_RegistrySlot
import R1Z.PV_Inv_PoleMass
set_option autoImplicit false
namespace R1Z.PV_Inv_RegistryNoPole
open R0P R0Z.HonestValidity
variable {K : Type} [Field K]
attribute [local irreducible] copyLinks copyPatterns copyActiveRowMasks copyInactiveRows

theorem producer (t : Trace K) (lambda chi : K) (link : CopyLink) (member : link ∈ copyLinks)
    (active : CopyActiveRow link.producer.row) (safe : NoPole t lambda chi) :
    chi ≠ copyTupleValue lambda (copyEndpointTuple t link.tag link.producer) := by
  rw [←PV_Inv_RegistrySlot.producer t lambda link member]
  exact (safe link.producer.row active link.producer.slot).1

theorem consumer (t : Trace K) (lambda chi : K) (link : CopyLink) (member : link ∈ copyLinks)
    (active : CopyActiveRow link.consumer.row) (safe : NoPole t lambda chi) :
    chi ≠ copyTupleValue lambda (copyEndpointTuple t link.tag link.consumer) := by
  rw [←PV_Inv_RegistrySlot.consumer t lambda link member]
  exact (safe link.consumer.row active link.consumer.slot).2

#print axioms producer
#print axioms consumer
end R1Z.PV_Inv_RegistryNoPole
