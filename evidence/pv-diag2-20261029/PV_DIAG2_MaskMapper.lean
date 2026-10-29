import PV_DIAG2_Retry
set_option autoImplicit false
namespace PV_DIAG2
open Aeneas Aeneas.Std Result ProverRwFull

def isMaskExhausted : aspis_prover.state_only_hiding.StateOnlyMaskBuildError → Bool
 | .MaskSampleExhausted => true
 | _ => false

theorem mask_mapper_exact (e : aspis_prover.state_only_hiding.StateOnlyMaskBuildError) :
 prover.mask_error e = ok (if isMaskExhausted e then .Rejected else .Semantic) := by
 cases e <;> simp [prover.mask_error,isMaskExhausted,
   aspis_prover.state_only_hiding.StateOnlyMaskBuildError.Insts.CoreCmpPartialEqStateOnlyMaskBuildError.eq,
   aspis_prover.state_only_hiding.StateOnlyMaskBuildError.read_discriminant]

/-- The native mapper's complete local control is a unit-enum comparison and
return; producing the mask error and the caller's diagnostics remain separate. -/
def maskMapperExecution (e : aspis_prover.state_only_hiding.StateOnlyMaskBuildError) :
 Execution verifier.Error := ⟨[],.value (if isMaskExhausted e then .Rejected else .Semantic)⟩

theorem mask_mapper_silent (e : aspis_prover.state_only_hiding.StateOnlyMaskBuildError) :
 (maskMapperExecution e).effects = [] := rfl

theorem mask_branch_public (e f : aspis_prover.state_only_hiding.StateOnlyMaskBuildError)
    (sameBranch : isMaskExhausted e = isMaskExhausted f) :
 maskMapperExecution e = maskMapperExecution f := by
 simp only [maskMapperExecution,sameBranch]

#print axioms mask_mapper_exact
#print axioms mask_mapper_silent
#print axioms mask_branch_public
end PV_DIAG2
