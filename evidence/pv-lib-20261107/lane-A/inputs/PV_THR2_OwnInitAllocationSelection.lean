import PV_THR2_OwnUniformReceiverFrame
set_option autoImplicit false
noncomputable section
namespace PV_THR2_OwnInitAllocationSelection
open PV_EVHB_OwnerMachine PV_EVHB_RawVecOwner
/-- Conditional on owner acceptance of amended translator. Hypotheses: none.
The last source-minted descriptor is selected without using any allocator reply.
The finite registered phase must establish that no second mint intervened. -/
def id (s : OWNER) : Nat := s.next-1
/-- Conditional on owner acceptance of amended translator. Hypothesis: the
trace-derived receiver frame, including its source-minted next-id component.
Resolve the exact allocation id/header, not an endpoint receiver assumption. -/
theorem selected {a oid : Nat} {h : Header} {s : OWNER}
    (frame : PV_THR2_OwnUniformReceiverFrame.Frame a oid h s) :
    id s = oid ∧ lookup s.world (id s) = some h := by
  have eq : id s = oid := by simp only [id,frame.next,Nat.add_sub_cancel]
  exact ⟨eq,by rw [eq]; exact frame.header⟩
/-- Conditional on owner acceptance of amended translator. Hypotheses: none.
At actual14320 the selection derives from the native frame's activation/local45
and original next-id; allocation14756 supplies neither a place nor a new id. -/
theorem binding (store : PV_STX2_Store.Store PV_STX2_Syntax.Data) (a : Nat)
    (parents : List PV_STX2_SliceMachine.Frame) (s : OWNER) :
    let c : PV_STX2_SliceMachine.Config :=
      ⟨{activation := a,remaining := PV_THR2_F361.live.body.drop 113},parents,store⟩
    let pre := PV_THR2_BindingRegister.register c s
    id pre = s.next ∧ lookup pre.world (id pre) =
      some (PV_EVHB_SourceLifetimes.emptyHeader PV_THR2_BoxRegister.shape 8) :=
  selected (PV_THR2_OwnUniformReceiverFrame.registered store a parents s).2
#print axioms selected
#print axioms binding
end PV_THR2_OwnInitAllocationSelection
