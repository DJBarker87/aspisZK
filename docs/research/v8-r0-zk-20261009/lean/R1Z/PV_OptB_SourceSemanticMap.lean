import R1Z.PV_OptB_SourceRetryStep
set_option autoImplicit false
namespace R1Z.PV_OptB_SourceSemanticMap
open Aeneas Aeneas.Std Result ProverRwFull
variable [ExternalTypes] [ExternalFuns]

/-- The external equality law is P work; it is not inferred merely from the
derived equality operation's name. -/
theorem rejected_of_active_pole
    (equal : r1_wire.Error.Insts.CoreCmpPartialEqError.eq .ActivePole .ActivePole = .ok true) :
    prover.semantic_error .ActivePole = .ok .Rejected := by
  rw [prover.semantic_error,equal]
  rfl

theorem semantic_of_other (error : r1_wire.Error)
    (different : r1_wire.Error.Insts.CoreCmpPartialEqError.eq error .ActivePole = .ok false) :
    prover.semantic_error error = .ok .Semantic := by
  rw [prover.semantic_error,different]
  rfl

#print axioms rejected_of_active_pole
#print axioms semantic_of_other
end R1Z.PV_OptB_SourceSemanticMap
