import R1Z.PV_RunJoin_BuiltHelper72
import R1Z.PV_RunJoin_NativeAfterBuild55
import R1Z.PV_RunJoin_ActualProvenance60
import R1Z.PV_RunJoin_CaptureBoundary61
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_CaptureTail72
open Aeneas Aeneas.Std Result ProverRwFull PV_RunJoin_WeightInstalled46

theorem complete (base : ExternalTypes) (heap : Heap) (box : Box)
    (ops : @ExternalFuns (types base)) {T : Type}
    (public1 : @aspis_statement.pool_v1.pair_forest_semantic_terminal.r0.Public (types base))
    (hash : aspis_core.digest.LegacyHashFn) (variant : transport.Variant)
    (backend : prover.Backend)
    (reserved : aspis_prover.state_only_entropy.ReservedStateOnlyAttemptSecrets)
    (context : aspis_core.state_only_hiding.StateOnlyHidingContext)
    (audit : prover.MaskedFixtureAudit) (store : T)
    (built : host_semantic.BuiltSemantics aspis_core.digest.LegacyHashFn)
    (balanced : @PV_RunJoin_BuiltHelper72.Balanced (types base) (selected base heap box ops) _ built) :
    letI : ExternalTypes := types base
    @PV_RunJoin_NativeAfterBuild55.run (types base) (selected base heap box ops) _ T
      PV_RunJoin_ActualProvenance60.capture public1 variant hash backend reserved context audit store (.Ok built)=
      ok (.Ok (⟨public1,variant,hash,backend,built,(reserved,context)⟩,
        {audit with h1_total_balanced:=true}),store) := by
  letI : ExternalTypes := types base
  letI : ExternalFuns := selected base heap box ops
  obtain ⟨h,o,q,hr,ho,hq,heq⟩ := balanced
  have hm : core.result.Result.map_err (BuiltinFnOnce r1_wire.Error verifier.Error)
      (.Ok built) prover.semantic_error=ok (.Ok built) := by
    rw [PV_RunJoin_CaptureBoundary61.selected_mapErr base heap box ops]
    rfl
  simp only [PV_RunJoin_NativeAfterBuild55.run,hm,
    core.result.Result.Insts.CoreOpsTry.branch,bind_tc_ok,hr,ho,hq,heq,
    if_true,PV_RunJoin_ActualProvenance60.capture]

#print axioms complete
end R1Z.PV_RunJoin_CaptureTail72
