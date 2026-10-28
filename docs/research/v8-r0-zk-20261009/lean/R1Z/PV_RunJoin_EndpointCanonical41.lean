import R1Z.PV_RunJoin_EndpointPost41
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_EndpointCanonical41
open Aeneas Aeneas.Std Result ProverRwFull
open PV_RunJoin_PolyCell38 PV_RunJoin_ResultPost41 PV_RunJoin_HighDomain40
variable [ExternalTypes]

/-- A theorem about every actual endpoint_bytes source Result. It asserts
length and canonicality on success; it neither asserts success nor changes
any failed/divergent Result or world. -/
theorem post (ops : ExternalFuns) (columns : Array (alloc.vec.Vec Q) 29#usize)
    (variant : transport.Variant) (z : aspis_core.circle.SecureCirclePoint) :
    Post (fun next : alloc.vec.Vec U8 => next.length=928 ∧ HighZero next.val)
      (@host_semantic.endpoint_bytes _ (ProverRwP6BodyCandidate.selected ops)
        columns variant z) := by
  have empty : HighZero ([] : List U8) := by
    intro k j bound lo hi
    simp only [List.length_nil] at bound
    omega
  exact PV_RunJoin_EndpointPost41.loop ops columns variant z 29 0#usize
    (alloc.vec.Vec.with_capacity U8 928#usize) rfl
    (by change 0+32*29≤Usize.max;scalar_tac) rfl empty

theorem success (ops : ExternalFuns) (columns : Array (alloc.vec.Vec Q) 29#usize)
    (variant : transport.Variant) (z : aspis_core.circle.SecureCirclePoint)
    (next : alloc.vec.Vec U8)
    (h : @host_semantic.endpoint_bytes _ (ProverRwP6BodyCandidate.selected ops)
      columns variant z=.ok next) : next.length=928 ∧ HighZero next.val :=
  PV_RunJoin_ResultPost41.success _ _ next (post ops columns variant z) h
#print axioms post
#print axioms success
end R1Z.PV_RunJoin_EndpointCanonical41
