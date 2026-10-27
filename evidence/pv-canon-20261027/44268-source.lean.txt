import R1Z.PV_Canon_Rounds
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_Canon
open Aeneas Aeneas.Std Result ProverRwFull
/-- Whole extracted sumcheck caller equals its proof-only domain-monitored
version at the named selected dictionary. Native deployment association is
not a premise silently discharged by this theorem. -/
theorem prover_checked (base : ExternalTypes)
    (ops : @ExternalFuns (PV_Join_PublicCaller.native base))
    {H F : Type} (digest : aspis_core.digest.Digest32 H) (oracleInst : host_sumcheck.Oracle F)
    (s : host_wire.SemanticTranscript H) (output : alloc.vec.Vec U8)
    (initial : aspis_core.field.QM31) (oracle : F) :
    @host_sumcheck.prove_sumcheck (PV_Join_PublicCaller.native base)
      (PV_Join_PublicCaller.selected base ops) H F digest oracleInst s output initial oracle =
    @checked_prover (PV_Join_PublicCaller.native base)
      (PV_Join_PublicCaller.selected base ops) H F digest oracleInst s output initial oracle := by
  letI : ExternalTypes := PV_Join_PublicCaller.native base
  letI : ExternalFuns := PV_Join_PublicCaller.selected base ops
  unfold host_sumcheck.prove_sumcheck checked_prover
  apply bind_congr_all; intro zero
  exact rounds_checked base ops digest oracleInst 10 s output _ initial 0#usize oracle rfl
#print axioms prover_checked
end R1Z.PV_Canon
