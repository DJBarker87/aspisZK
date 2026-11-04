import NFG_QueryLoopSource
set_option autoImplicit false
namespace AspisR1.NFP_LoopBudget
open Aeneas Aeneas.Std Result AspisR1Stage2 NFG_QueryLoopDefs
/-- TX1 and TX2 use their actual end bounds; no whole-loop native unwind. -/
theorem tx1 (a : A) (b : B) (inside : a.next.val≤10) :
 Budget 10#usize (10-a.next.val) (.Ok (a,b)) := by
 change 10 ≤ a.next.val+(10-a.next.val)
 omega

theorem tx2 (a : A) (b : B) (inside : a.next.val≤22) :
 Budget 22#usize (22-a.next.val) (.Ok (a,b)) := by
 change 22 ≤ a.next.val+(22-a.next.val)
 omega

theorem maximum (a : A) (b : B) (finish : Usize) :
 Budget finish finish.val (.Ok (a,b)) := by
 change finish.val ≤ a.next.val+finish.val
 omega
#print axioms tx1
#print axioms tx2
#print axioms maximum
end AspisR1.NFP_LoopBudget
