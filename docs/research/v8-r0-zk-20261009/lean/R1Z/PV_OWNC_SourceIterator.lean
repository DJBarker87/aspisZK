import R1Z.PV_OWNB_SnapshotResult
set_option autoImplicit false
namespace R1Z.PV_OWNC_SourceIterator
open PV_OWNB_Cursor PV_OWN_Link
/-- Non-ZST IntoIter header, in byte addresses. Source and destination Link
have size 8, alignment 2. The owner/generation is the Cursor token. -/
structure Header where
 buf : Nat
 ptr : Nat
 endPtr : Nat
 cap : Nat
 deriving DecidableEq

def header (q : Cursor) : Header :=
 ⟨q.token.address,q.token.address+q.read*8,q.token.address+q.length*8,q.capacity⟩

/-- IntoIter::next advances before reading old; try_fold reads old then
advances before the callback. Link POD makes these equivalent at the callback. -/
def next (q : Cursor) : Option Link × Cursor :=
 if q.read=q.length then (none,q) else (some (q.source q.read),advance q)

theorem exhausted (q : Cursor) (h:q.read=q.length) : next q=(none,q) := by
 simp only [next,h,ite_true]

theorem available (q : Cursor) (h:q.read≠q.length) :
 next q=(some (q.source q.read),advance q) := by
 simp only [next,h,ite_false]

theorem pointer_exhausted (q : Cursor) :
 (header q).ptr=(header q).endPtr ↔ q.read=q.length := by
 simp only [header]
 omega
#print axioms exhausted
#print axioms available
#print axioms pointer_exhausted
end R1Z.PV_OWNC_SourceIterator
