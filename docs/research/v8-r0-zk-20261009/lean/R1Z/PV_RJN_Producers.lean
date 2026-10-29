import R1Z.PV_RunJoin_PublishContext57
set_option autoImplicit false
namespace R1Z.PV_RJN_Producers
open Aeneas Aeneas.Std Result ProverRwFull PV_RunJoin_PublishSkeleton54
variable [ExternalTypes] [ExternalFuns]
/-- The plan's literal header and three offsets agree with the constants read
by the native serializer. No publication or assembly equation is assumed. -/
def PV_RJN_Producer_Layout {I : Type} (runs : I → Run) : Prop :=
  ∀ i, ∃ (size openings nodes : Usize) (magic : Array U8 8#usize) (tag : U8),
    compact.PROOF_BYTES=ok size ∧ compact.OFF_OPENINGS=ok openings ∧ compact.OFF_NODES=ok nodes ∧
    compact.MAGIC=ok magic ∧ transport.Variant.tag .S2=ok tag ∧
    (runs i).plan.proofBytes=size.val ∧ (runs i).plan.offOpenings=openings.val ∧
    (runs i).plan.offNodes=nodes.val ∧
    (runs i).plan.header=bytes magic.val++bytes [tag,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8]

/-- Room for the two compact front encoders. The remaining append bounds are
recovered from successful source calls, rather than assumed. -/
def PV_RJN_Producer_FrontRoom {I : Type} (runs : I → Run) : Prop :=
  ∀ i, (runs i).plan.header.length+(runs i).plan.semantic.length+(runs i).plan.claim.length≤Usize.max

#print axioms PV_RJN_Producer_Layout
#print axioms PV_RJN_Producer_FrontRoom
end R1Z.PV_RJN_Producers
