import R1Z.PV_OWNC_SourceIdentity
set_option autoImplicit false
namespace R1Z.PV_OWNC_InPlaceResult
open PV_OWNB_Cursor PV_OWN_Link PV_OWNC_GuardState PV_OWN_Operations
/-- Compose reader, sink and two ownership moves. The source header is reset
before the saved POD tail is dropped. No shrink branch is selected for Link.
This is the in-place filtering stage, not the subsequent forest callback. -/
theorem guarded (q : Cursor) (keep : Link → Bool) (h:PV_OWNB_Cursor.Valid q)
 (guard result : Nat) (ge:q.memory.slots guard=none) (re:q.memory.slots result=none)
 (gs:guard≠q.owner) (rs:result≠q.owner) (rg:result≠guard) :
 let filtered:=PV_OWNC_SourceLoop.run keep (q.length-q.read) q
 let guarded:=handoff filtered guard
 let returned:=handoff guarded result
 PV_OWNB_Cursor.Valid returned ∧
 returned.token=q.token ∧ returned.memory.slots guard=none := by
 dsimp only
 have hi:=PV_OWNC_SourceIdentity.loop keep (q.length-q.read) q
 have hf:PV_OWNB_Cursor.Valid (PV_OWNC_SourceLoop.run keep (q.length-q.read) q):=
  (PV_OWNC_SourceLoop.completed keep q h).1
 let filtered:=PV_OWNC_SourceLoop.run keep (q.length-q.read) q
 have hge:filtered.memory.slots guard=none := by rw [hi.2.2.1];exact ge
 have hgs:guard≠filtered.owner := by rw [hi.1];exact gs
 have hg:=PV_OWNC_GuardValid.valid filtered hf guard hge hgs
 have hrs:result≠filtered.owner := by rw [hi.1];exact rs
 have hfe:filtered.memory.slots result=none := by rw [hi.2.2.1];exact re
 have hre:(handoff filtered guard).memory.slots result=none := by
  simp only [handoff,move,hrs,
   rg,ite_false]
  exact hfe
 exact ⟨PV_OWNC_GuardValid.valid _ hg result hre rg,hi.2.1,
  PV_OWNC_GuardTransfer.source_consumed (handoff filtered guard) result⟩
#print axioms guarded
end R1Z.PV_OWNC_InPlaceResult
