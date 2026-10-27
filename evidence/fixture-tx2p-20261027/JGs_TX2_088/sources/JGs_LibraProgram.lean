import FJm_LibraStages
set_option autoImplicit false
noncomputable section
namespace AspisR1.JGs_LibraProgram
open Aeneas Aeneas.Std Result ControlFlow
open FIo_FieldBridge (NE NQ)
open FJm_LibraStages (Weights State)
def body (ap0 ap1 : Weights) (extra : Array NQ 2#usize)
    (iter : FIo_RangeNext.Range) (weights : Weights) : Result (ControlFlow State Weights) := do
  let (o,cursor) ← core.iter.range.IteratorRange.next core.iter.range.StepUsize iter
  match o with
  | none => ok (.done weights)
  | some side => do
    let (base,high,q4,q16) ← FJm_LibraStages.powers extra side
    let low ← FIo_Native.weights.Weights.scalar_factor base ap0
    let (_,t0) ← FJm_LibraStages.term ap1 high 0#usize
    let (_,t1) ← FJm_LibraStages.term ap1 high 1#usize
    let (_,t2) ← FJm_LibraStages.term ap1 high 2#usize
    let (i3,t3) ← FJm_LibraStages.term ap1 high 3#usize
    let (first2,first3,all) ← FJm_LibraStages.totals (Array.make 4#usize [t0,t1,t2,t3])
    FJm_LibraStages.finish side low i3 first2 first3 all q4 q16 ap1 weights cursor
/-- Symbolic factoring only: no concrete native arithmetic is reduced here. -/
theorem source (ap0 ap1 : Weights) (extra : Array NQ 2#usize)
    (iter : FIo_RangeNext.Range) (weights : Weights) :
    FIo_Native.weights.factored_s2_libra_weights_loop.body ap0 ap1 extra iter weights=
      body ap0 ap1 extra iter weights := by
  unfold FIo_Native.weights.factored_s2_libra_weights_loop.body body
    FJm_LibraStages.powers FJm_LibraStages.term FJm_LibraStages.totals FJm_LibraStages.finish
  simp only [bind_assoc_eq,bind_tc_ok,Aeneas.Std.uncurry]
#print axioms source
end AspisR1.JGs_LibraProgram
end
