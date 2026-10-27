import R1Z.ProverRw19P6ContextIdentity
set_option autoImplicit false
noncomputable section
namespace R1Z.ProverRw21Op223Boundary
open Aeneas Aeneas.Std Result ProverRwFull
variable [ExternalTypes]

-- An artificial dictionary witness, never a purported shipped implementation.
-- It explains why the original dictionary's concrete source association is
-- necessary; it is not a counterexample against shipped Rust and is not a stop.
def diverging (ops : ExternalFuns) : ExternalFuns :=
  {ops with op223 := fun _ _ _ => .div}

theorem association_required (ops : ExternalFuns) (tag : U32)
    (values : Slice U32) (lambda : aspis_core.field.QM31) :
    (diverging ops).op223 ≠
      @ProverRwP6CompressSource.compress _ (PV_CurrentScaleInstall.selected (diverging ops)) := by
  intro same
  have h := congrFun (congrFun (congrFun same tag) values) lambda
  obtain ⟨final,hf⟩ := ProverRw18ContextTotal.total (diverging ops) tag values lambda
  rw [← ProverRw19P6ContextIdentity.identity (diverging ops)] at hf
  have impossible : (Result.div : Result aspis_core.field.QM31)=.ok final := h.trans hf
  cases impossible

#print axioms diverging
#print axioms association_required
end R1Z.ProverRw21Op223Boundary
