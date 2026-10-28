import R1Z.PV_RunJoin_CoefficientArray44
import R1Z.ProverRwP6BodyCandidate
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_CoefficientInstalled44
open Aeneas Aeneas.Std Result ProverRwFull
variable [ExternalTypes]

theorem source (ops : ExternalFuns) {T : Type} (copy : core.marker.Copy T) (rows : Array T 1024#usize) :
    @transport.Variant.coefficients _ (ProverRwP6BodyCandidate.selected ops) T copy .S2 rows =
      ProverRwSuccessCoefficientsSource.transport.Variant.coefficients copy .S2 rows := rfl

theorem complete (ops : ExternalFuns) {T : Type} (copy : core.marker.Copy T) (xs : Nat → T) :
    @transport.Variant.coefficients _ (ProverRwP6BodyCandidate.selected ops) T copy .S2
      (ProverCommitArray49.array 1024#usize xs) =
      .ok (ProverCommitArray49.array 1024#usize (fun j => xs (AspisR1.rowNat j))) := by
  rw [source ops copy (ProverCommitArray49.array 1024#usize xs)]
  exact PV_RunJoin_CoefficientArray44.complete copy ProverRwSuccessCoefficientsSource.transport.Variant.S2 xs
#print axioms source
#print axioms complete
end R1Z.PV_RunJoin_CoefficientInstalled44
