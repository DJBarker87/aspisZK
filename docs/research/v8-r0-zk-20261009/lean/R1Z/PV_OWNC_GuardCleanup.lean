import R1Z.PV_OWNC_GuardValid
set_option autoImplicit false
namespace R1Z.PV_OWNC_GuardCleanup
open PV_OWNB_Cursor PV_OWNC_GuardState PV_OWN_Operations PV_W_Threading
/-- InPlaceDrop destroys only initialized destination elements; Link is POD.
InPlaceDstDataSrcBufDrop creates RawVec<Src> before dropping the headDrop, so
its eventual free uses the original source capacity and alignment. -/
def headDrop {S X E : Type} : Action S X E Unit := dropPod

def destination {S X E : Type}
 (dealloc : Nat → Request → S → Outcome E Unit × S) (q : Cursor) : Action S X E Unit :=
 bind headDrop (fun _=>PV_OWNB_CursorCleanup.cleanup dealloc q)

theorem prefix_empty {S X E : Type} (w : State S X) :
 (headDrop (E:=E) w).outcome=.ok () ∧ (headDrop (E:=E) w).world=w ∧
 (headDrop (E:=E) w).calls=[] := ⟨rfl,rfl,rfl⟩

theorem original_layout {S X E : Type}
 (dealloc : Nat → Request → S → Outcome E Unit × S) (q : Cursor)
 (h:PV_OWNB_Cursor.Valid q) (s : S) (x : X) (nz:q.cell.size≠0) :
 (destination dealloc q ⟨q.memory,s,x⟩).calls=
 [(⟨take q.owner q.memory,s,x⟩,.deallocate q.token.address q.cell.size q.cell.alignment)] := by
 simpa only [destination,headDrop,dropPod,lift,PV_W_Threading.bind,List.nil_append] using
  PV_OWNB_CursorCleanup.positive dealloc q h s x nz
#print axioms prefix_empty
#print axioms original_layout
end R1Z.PV_OWNC_GuardCleanup
