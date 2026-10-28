import R1Z.ProverRwP6BoundarySource
set_option autoImplicit false
noncomputable section
namespace R1Z.ProverRwP6BoundaryStep
open Aeneas Aeneas.Std Result ProverRwFull
abbrev Acc := ProverRwP6BoundarySource.BoundaryAcc
abbrev Q := aspis_core.field.QM31
-- Pure wrapping update. Accumulators remain symbolic, even in 27-step clients.
def advance (x : Q) (s : Acc) : Acc :=
  { a := U64.wrapping_add s.a (UScalar.cast .U64 x.c0.a),
    b := U64.wrapping_add s.b (UScalar.cast .U64 x.c0.b),
    c := U64.wrapping_add s.c (UScalar.cast .U64 x.c1.a),
    d := U64.wrapping_add s.d (UScalar.cast .U64 x.c1.b) }
theorem step (x : Q) (s : Acc) :
    ProverRwP6BoundarySource.boundary_acc_step x s = ok (advance x s) := rfl
theorem total (x : Q) (s : Acc) :
    ∃ out, ProverRwP6BoundarySource.boundary_acc_step x s = ok out := ⟨_, step x s⟩
#print axioms step
#print axioms total
end R1Z.ProverRwP6BoundaryStep
