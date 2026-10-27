import R1Z.ProverRwFullFuns
set_option autoImplicit false
namespace R1Z.PDict_MaskError
open Aeneas Aeneas.Std Result ProverRwFull

theorem mask_error
    (e : aspis_prover.state_only_hiding.StateOnlyMaskBuildError) :
    prover.mask_error e =
      .ok (match e with
        | .MaskSampleExhausted => verifier.Error.Rejected
        | _ => verifier.Error.Semantic) := by
  cases e <;> simp [prover.mask_error,
    aspis_prover.state_only_hiding.StateOnlyMaskBuildError.Insts.CoreCmpPartialEqStateOnlyMaskBuildError.eq,
    read_discriminant,
    aspis_prover.state_only_hiding.StateOnlyMaskBuildError.read_discriminant]

#print axioms mask_error
end R1Z.PDict_MaskError
