import R1Z.PV_CB_CompressSupport
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_CB_Op223Boundary
open Aeneas Aeneas.Std Result ProverRwFull
variable [ExternalTypes]
abbrev M := aspis_core.field.M31
abbrev Q := aspis_core.field.QM31

/-- Changing only the open callback leaves the independent P6 reference unchanged. -/
theorem reference_independent (ops : ExternalFuns)
    (f g : M → Slice M → Q → Result Q) (tag : M) (values : Slice M) (lambda : Q) :
    @ProverRwP6CompressSource.compress _
      {ops with op223 := f} tag values lambda =
    @ProverRwP6CompressSource.compress _
      {ops with op223 := g} tag values lambda := by
  apply PV_CB_CompressSupport.congr <;> rfl

/-- A model boundary check, not a shipped Rust counterexample.  The source
    binding must restrict or replace the open callback; arithmetic installation
    alone cannot prove this universal callback equation. -/
theorem no_universal_binding (ops : ExternalFuns) (tag : M) (values : Slice M) (lambda : Q) :
    ¬ (∀ callbacks : ExternalFuns, callbacks.op223 tag values lambda =
      @ProverRwP6CompressSource.compress _ callbacks
        tag values lambda) := by
  intro h
  have left := h {ops with op223 := fun _ _ _ => .fail .panic}
  have right := h {ops with op223 := fun _ _ _ => .div}
  have independent := reference_independent ops
    (fun _ _ _ => .fail .panic) (fun _ _ _ => .div) tag values lambda
  have impossible : (Result.fail Error.panic : Result Q) = .div :=
    left.trans (independent.trans right.symm)
  cases impossible
#print axioms reference_independent
#print axioms no_universal_binding
end R1Z.PV_CB_Op223Boundary
