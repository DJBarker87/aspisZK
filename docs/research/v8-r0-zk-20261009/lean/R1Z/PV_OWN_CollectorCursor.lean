import R1Z.PV_OWN_Bytes
set_option autoImplicit false
namespace R1Z.PV_OWN_CollectorCursor
open PV_OWN_Bytes
/-- Equal-sized in-place compaction never writes into an unread later cell. -/
theorem before_unread (width read write next : Nat) (compact:write≤read) (unread:read<next) :
 write*width+width≤next*width := by
 have a:=Nat.mul_le_mul_right width (Nat.succ_le_succ compact)
 have b:=Nat.mul_le_mul_right width unread
 simp only [Nat.succ_mul] at a b
 omega

theorem future_byte (old value : Bytes) (width read write next j : Nat)
 (compact:write≤read) (unread:read<next) :
 overwrite old (write*width) width value (next*width+j)=old (next*width+j) := by
 apply outside
 right
 have h:=before_unread width read write next compact unread
 omega

/-- Filtering a rejected item advances only the input cursor. -/
theorem reject_progress (read write : Nat) (compact:write≤read) : write≤read+1 := by omega
/-- Keeping one item advances both cursors and preserves compaction. -/
theorem keep_progress (read write : Nat) (compact:write≤read) : write+1≤read+1 := by omega
#print axioms before_unread
#print axioms future_byte
#print axioms reject_progress
#print axioms keep_progress
end R1Z.PV_OWN_CollectorCursor
