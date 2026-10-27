import R1Z.PDict_RemainingCommute231_39
set_option autoImplicit false
noncomputable section
namespace R1Z.PDict_RemainingCaller231
open Aeneas Aeneas.Std Result ProverRwFull
open PDict_RemainingDictionary231 (native selected)
open PDict_RemainingExt231 (replace)

theorem dictionary_independent (base : ExternalTypes)
    (ops other : @ExternalFuns (native base)) :
    selected base (@replace (native base) ops other) = selected base ops := by
  letI : ExternalTypes := native base
  let upd (d : @ExternalFuns (native base)) : @ExternalFuns (native base) :=
    { d with
      op78 := @ProverRwP7FibreSource.fibre
      op231 := PDict_RemainingLeafSource.aspis_statement.state_only_trace.StateOnlyTraceFoundation.Insts.CoreCloneClone.clone
      op247 := PDict_RemainingLeafSource.aspis_r1_cost_probe.trace.value }
  have hu (d : @ExternalFuns (native base)) :
      upd (@replace (native base) d other) = upd d := by rfl
  change upd (PDict_CodecDictionary.selected base (@replace (native base) ops other)) =
    upd (PDict_CodecDictionary.selected base ops)
  exact (congrArg upd (PDict_RemainingCommute231.stage39 base ops other)).trans
    (hu (PDict_CodecDictionary.selected base ops))

/-- The actual proof-account caller, all arguments and Result outcomes, at
this fixed carrier/source dictionary. Native world and trace refinement
remain separate. No store/retry carrier lift is used. -/
theorem client_independent (base : ExternalTypes)
    (ops other : @ExternalFuns (native base)) :
    @RealR1_client.prove_for_proof_accounts (native base)
      (selected base (@replace (native base) ops other)) =
    @RealR1_client.prove_for_proof_accounts (native base) (selected base ops) := by
  exact congrArg (fun d : @ExternalFuns (native base) =>
    @RealR1_client.prove_for_proof_accounts (native base) d)
    (dictionary_independent base ops other)

#print axioms dictionary_independent
#print axioms client_independent
end R1Z.PDict_RemainingCaller231
