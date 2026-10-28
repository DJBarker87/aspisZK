import R1Z.PV_RunJoin_CoefficientsThread45
import R1Z.PV_RunJoin_Vector44
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_CoefficientsCell45
open Aeneas Aeneas.Std Result ProverRwFull
variable [ExternalTypes]
open PV_RunJoin_CoefficientsThread45 (Column)
set_option allowUnsafeReducibility true in
attribute [local irreducible] ProverRwP6BoundaryInstall.selected

theorem step (ops : ExternalFuns) (messages : Slice Column) (out : alloc.vec.Vec Column)
    (lane : Usize) (p : Nat → aspis_core.field.wide_exact.WideExact)
    (read : Slice.index_usize messages lane = .ok (ProverCommitArray49.array 1024#usize p)) :
    @PV_RunJoin_CoefficientsThread45.step _ (ProverRwP6BodyCandidate.selected ops) .S2 messages out lane =
      alloc.vec.Vec.push out (ProverCommitArray49.array 1024#usize (fun j => p (AspisR1.rowNat j))) := by
  unfold PV_RunJoin_CoefficientsThread45.step
  rw [read]
  simp only [bind_tc_ok]
  exact congrArg (fun r : Result Column => r >>= alloc.vec.Vec.push out)
    (PV_RunJoin_CoefficientInstalled45.complete ops (@aspis_core.field.wide_exact.WideExact.Insts.CoreMarkerCopy _ (ProverRwP6BodyCandidate.selected ops)) p)
#print axioms step
end R1Z.PV_RunJoin_CoefficientsCell45
