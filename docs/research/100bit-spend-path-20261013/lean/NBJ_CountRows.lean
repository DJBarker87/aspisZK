import NBI_CountPort
import NBJ_Opening

set_option autoImplicit false
namespace AspisR1.NBJ_CountRows
open MultiproofConeLiveOrder MultiproofConeCountPhysical
attribute [local instance] Classical.propDecidable

/-- Source-order count rows use the equal-parent inner scan before the write.
The already consumed array suffix is arbitrary. -/
def nativeRows : Nat → (Nat → Nat) → Nat → Nat → Nat → Nat → List Nat × Nat
  | 0,key,_,_,w,count => (cells key 0 w,count)
  | fuel+1,key,n,i,w,count =>
      if i < n then
        let j := NBI_CountScan.scan key (key i/2) n (n-i) i
        nativeRows fuel (write key i w) n j (w+1) (count+(2-(j-i)))
      else (cells key 0 w,count)

/-- Total row induction associates the source scan/write recurrence with the
installed physical count recurrence. Each unread-order precondition is derived
for the next row; no final count or live-prefix equation is assumed. -/
theorem rows_port (fuel : Nat) (key : Nat → Nat) (n i w count : Nat)
    (safe : w ≤ i) (endBound : i ≤ n) (ordered : Strict key i n) :
    nativeRows fuel key n i w count =
      MultiproofConeCountPhysical.rows fuel key n i w count := by
  induction fuel generalizing key i w count with
  | zero => rfl
  | succ fuel ih =>
    by_cases active : i < n
    · have step := NBI_CountPort.scan_row key n i active ordered
      have advanceBounds := advance_bounds key n i active
      have nextOrder : Strict (write key i w) (advance key n i) n := by
        intro a b lo asc hi
        have aw : a ≠ w := by omega
        have bw : b ≠ w := by omega
        simp only [write,if_neg aw,if_neg bw]
        exact ordered a b (by omega) asc hi
      have contribution : 2-(advance key n i-i) = (if pairAt key n i then 0 else 1) := by
        simpa only [step.1] using step.2
      simp only [nativeRows,MultiproofConeCountPhysical.rows,if_pos active,step.1,contribution]
      exact ih (write key i w) (advance key n i) (w+1) _ (by omega) advanceBounds.2 nextOrder
    · simp only [nativeRows,MultiproofConeCountPhysical.rows,if_neg active]

/-- One complete source level projects to the existing symbolic count level. -/
theorem level_port (key : Nat → Nat) (n : Nat) (ordered : Strict key 0 n) :
    nativeRows n key n 0 0 0 = OraclePortFrozenOrder.countLevel n (cells key 0 n) := by
  rw [rows_port n key n 0 0 0 (by omega) (by omega) ordered]
  exact level_projection key n

#print axioms rows_port
#print axioms level_port
end AspisR1.NBJ_CountRows
