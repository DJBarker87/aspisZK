import R1Z.PV_RunJoin_SemanticBound62
import R1Z.PV_RunJoin_ActualRun59
set_option autoImplicit false
namespace R1Z.PV_RunJoin_FrontProjection62
open Aeneas Aeneas.Std Result ProverRwFull PV_RunJoin_ResultPost41
variable [ExternalTypes] [ExternalFuns]

theorem semantic (p : prover.Publication) (layout : compact.LOGICAL_SEMANTIC=ok 13831#usize) :
    Post (fun out => out.length≤55*13831) (PV_RunJoin_ActualPlanSources59.compactSemantic p) := by
  have h := PV_RunJoin_SemanticBound62.encode (alloc.vec.Vec.deref p.semantic_bytes)
    PV_RunJoin_ActualPlanSources59.empty layout (by change 0+55*13831≤Usize.max;scalar_tac)
  unfold PV_RunJoin_ActualPlanSources59.compactSemantic
  cases he : host_compact.compact_semantic (alloc.vec.Vec.deref p.semantic_bytes)
      PV_RunJoin_ActualPlanSources59.empty with
  | fail e => trivial
  | div => trivial
  | ok pair =>
    rcases pair with ⟨status,next⟩
    rw [he] at h
    simp only [bind_tc_ok,Aeneas.Std.uncurry]
    cases status with
    | Err e => change 0≤55*13831;omega
    | Ok u => exact h

theorem publication (phase : PV_RunJoin_NativeControl55.Phase)
    (f : prover.Publication → Result (alloc.vec.Vec U8)) (bound : Nat)
    (law : ∀ p, Post (fun out => out.length≤bound) (f p)) :
    (PV_RunJoin_ActualPlanSources59.publicationBytes phase f).length≤bound := by
  unfold PV_RunJoin_ActualPlanSources59.publicationBytes
  cases hf : PV_RunJoin_ActualRunSources59.finish phase with
  | fail e => change 0≤bound;omega
  | div => change 0≤bound;omega
  | ok status =>
    cases status with
    | Err e => change 0≤bound;omega
    | Ok p =>
      cases he : f p with
      | fail e => change 0≤bound;omega
      | div => change 0≤bound;omega
      | ok out =>
        have h := law p
        rw [he] at h
        change (PV_RunJoin_PublishSkeleton54.bytes out.val).length≤bound
        rw [PV_RJN_Bytes.length]
        exact h

#print axioms semantic
#print axioms publication
end R1Z.PV_RunJoin_FrontProjection62
