import R1Z.PV_OWNC_AxiomsAudit
set_option autoImplicit false
namespace R1Z.PV_OWNC_FocusedReplay
open PV_OWNB_Cursor PV_OWN_Link PV_OWNC_GuardState
/-- Filtering-to-typed-Vec interface composition. This theorem still needs its
source instance and the later resource/value/store stages for whole-row V229. -/
theorem returned (q : Cursor) (h:PV_OWNB_Cursor.Valid q) (guard result : Nat)
 (ge:q.memory.slots guard=none) (re:q.memory.slots result=none)
 (gs:guard≠q.owner) (rs:result≠q.owner) (rg:result≠guard) :
 let filtered:=PV_OWNC_SourceLoop.run PV_OWNC_PathPredicate.keep (q.length-q.read) q
 let returned:=handoff (handoff filtered guard) result
 PV_OWNC_Vector.Valid PV_OWNB_LinkCodec.codec (PV_OWNC_CursorVector.vector returned) ∧
 returned.token=q.token ∧ returned.memory.slots guard=none := by
 have out:=PV_OWNC_InPlaceResult.guarded q PV_OWNC_PathPredicate.keep h guard result ge re gs rs rg
 exact ⟨PV_OWNC_CursorVector.initialized _ out.1,out.2⟩
#print axioms returned
end R1Z.PV_OWNC_FocusedReplay
