import NGM_FinishControl
set_option autoImplicit false
noncomputable section
namespace AspisR1.NGM_AcceptDecision
open Aeneas Aeneas.Std Result AspisR1Stage2 Port3_NativeFinishBody
open NGM_FinishControl
attribute [local instance] Classical.propDecidable
variable {W : Type}
/-- Deployed phase/value profiling hooks have no protocol effects. All
non-profiling operations retain their full Result, including fail/divergence. -/
def eraseProfiling (ops : Ops W) : Ops W :=
 {ops with op0:=fun _ _ _=>ok (),op1:=fun _ _=>ok ()}

def exactEquality (ops : Ops W) : Ops W :=
 {eraseProfiling ops with ne:=fun x y=>ok (decide (x≠y))}

theorem source_erased (ops : Ops W) (v : verifier.View) (p : verifier.Prepared)
 (a : verifier.Accumulator) :
 Port3_NativeFinishBody.verifier.finish_relation (eraseProfiling ops) v p a none =
 NGM_FinishControl.run (eraseProfiling ops) v p a none :=
 NGM_FinishControl.source _ _ _ _ _

/-- Exact final Result on both comparison branches; no equality or next=22
is assumed. This is the last gate, not the still-open enclosing finish call. -/
theorem final_result (ops : Ops W) (a : verifier.Accumulator) (actual : E) :
 afterDot (exactEquality ops) a none actual =
 ok (if a.next=22#usize ∧ actual=a.rhs then .Ok () else .Err verifier.Error.Query) := by
 classical
 by_cases next : a.next=22#usize <;> by_cases same : actual=a.rhs <;>
  simp [afterDot,exactEquality,eraseProfiling,next,same]

theorem final_accept_iff (ops : Ops W) (a : verifier.Accumulator) (actual : E) :
 afterDot (exactEquality ops) a none actual=ok (.Ok ()) ↔
 a.next=22#usize ∧ actual=a.rhs := by
 rw [final_result]
 by_cases accept : a.next=22#usize ∧ actual=a.rhs <;> simp [accept]
#print axioms source_erased
#print axioms final_result
#print axioms final_accept_iff
end AspisR1.NGM_AcceptDecision
end
