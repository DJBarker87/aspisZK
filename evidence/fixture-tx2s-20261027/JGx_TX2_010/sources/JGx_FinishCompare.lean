import Port3_FinishStage
set_option autoImplicit false
noncomputable section
namespace AspisR1.JGx_FinishCompare
open Aeneas Aeneas.Std Result AspisR1Stage2 AspisR1Stage2.Stage2Finish

def tail (a : verifier.Accumulator) (dot : E) : Result (core.result.Result Unit verifier.Error) := do
  if a.next != 22#usize then ok (.Err verifier.Error.Query)
  else do
    let different ← Port3_FinishStage.ne dot a.rhs
    if different then ok (.Err verifier.Error.Query) else ok (.Ok ())

theorem comparison (x : E) : Port3_FinishStage.ne x x=ok false := by
  simp only [Port3_FinishStage.ne,ne_eq,eq_self,not_true_eq_false,decide_false]
#print axioms comparison

theorem source (a : verifier.Accumulator) (next : a.next=22#usize) : tail a a.rhs=ok (.Ok ()) := by
  unfold tail
  rw [next]
  simp only [show (22#usize !=22#usize)=false from by decide,Bool.false_eq_true,ite_false]
  rw [comparison,bind_tc_ok]
  rfl
#print axioms source
end AspisR1.JGx_FinishCompare
end
