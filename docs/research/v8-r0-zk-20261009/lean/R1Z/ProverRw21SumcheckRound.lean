import R1Z.ProverRw21RoundLeaves
set_option autoImplicit false
noncomputable section
namespace R1Z.ProverRw21SumcheckRound
open Aeneas Aeneas.Std Result ProverRwFull ProverRw21Arity16Endpoint
variable [ExternalTypes]

theorem round (ops : ExternalFuns) (f g : Compression) :
    @host_sumcheck.prove_sumcheck_round _ {ops with op223 := f} =
      @host_sumcheck.prove_sumcheck_round _ {ops with op223 := g} := by
  funext H F D O transcript output point running index oracle
  simp only [host_sumcheck.prove_sumcheck_round,
    ProverRw21RoundLeaves.leaf0 ops f g,
    ProverRw21RoundLeaves.leaf1 ops f g,
    ProverRw21RoundLeaves.leaf2 ops f g,
    ProverRw21RoundLeaves.leaf3 ops f g,
    ProverRw21RoundLeaves.leaf4 ops f g]
  rfl
#print axioms round
end R1Z.ProverRw21SumcheckRound
