import NFP_LoopBudget
set_option autoImplicit false
noncomputable section
namespace AspisR1.NFP_Resume
open Aeneas Aeneas.Std Result AspisR1Stage2 NFG_QueryLoopDefs
open Port3_NativeQueryBody

theorem tx1 (ops : Ops) (proof : Slice U8) (p : verifier.Prepared)
 (a : verifier.Accumulator) (g : Array Stage2E 29#usize) (geometry : verifier.QueryGeometry)
 (b : verifier.BatchedWeights) (start : a.next.val=0) :
 run (fun a b => verifier.candidate.query_values ops proof p a g none geometry b)
  10#usize 10 (.Ok (a,b)) = verifier.candidate.query_loop ops proof p a g none geometry b 10#usize := by
 apply NFG_QueryLoopSource.complete
 change 10 ≤ a.next.val+10
 omega

theorem tx2 (ops : Ops) (proof : Slice U8) (p : verifier.Prepared)
 (a : verifier.Accumulator) (g : Array Stage2E 29#usize) (geometry : verifier.QueryGeometry)
 (b : verifier.BatchedWeights) (start : a.next.val=10) :
 run (fun a b => verifier.candidate.query_values ops proof p a g none geometry b)
  22#usize 12 (.Ok (a,b)) = verifier.candidate.query_loop ops proof p a g none geometry b 22#usize := by
 apply NFG_QueryLoopSource.complete
 change 22 ≤ a.next.val+12
 omega
#print axioms tx1
#print axioms tx2
end AspisR1.NFP_Resume
end
