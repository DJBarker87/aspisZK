import NGY_Oracle
set_option autoImplicit false
noncomputable section
namespace AspisR1.NGY_SourceStep
open Aeneas Aeneas.Std Result ControlFlow
open AspisR1CurrentPreparedClaim

def outcome {D H : Type} (iter : ClaimScalar.Range) (sem : r1_semantic.Verified H)
 (point : Usize) (after : D) (reply : core.result.Result Unit Unit) :
 ControlFlow (ClaimScalar.Range × r1_semantic.Verified H × Usize × D)
  (core.result.Result Concrete.E verifier.Error) :=
 match reply with
 | .Ok _ => .cont (iter,sem,point,after)
 | .Err _ => .done (.Err .Parse)

/-- Exact one-step G association, including Parse and arbitrary full poststate.
These are local child observations; no caller output equality is supplied. -/
theorem source {D H : Type} (ops : ClaimDotOps D) (inst : aspis_core.Digest32 H)
 (sem : r1_semantic.Verified H) (y1 : Slice U8) (g : Array Concrete.E 29#usize)
 (iter iter' : ClaimScalar.Range) (point lane : Usize) (before after : D)
 (value : Concrete.E) (scalar : aspis_core.field.QM31)
 (reply : core.result.Result Unit Unit)
 (next : core.iter.range.IteratorRange.next core.iter.range.StepUsize iter=ok (some lane,iter'))
 (read : ClaimScalar.read ops sem y1 point lane=ok scalar)
 (weight : Array.index_usize g lane=ok value)
 (push : ops.pushDot before value scalar=ok (reply,after)) :
 verifier.prepared_claim_dot_loop.body ops inst y1 g iter sem point before=
  ok (outcome iter' sem point after reply) := by
 rw [ClaimScalar.body_eq_source]
 simp only [ClaimScalar.body,next,bind_tc_ok,read,weight,push]
 cases reply with
 | Ok u => cases u; rfl
 | Err u => cases u; rfl

#print axioms source
end AspisR1.NGY_SourceStep
end
