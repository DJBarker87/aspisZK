import R1Z.PV_RunJoin_FinishContext47
import R1Z.PV_RunJoin_ResultPost
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_PublishReach54
open Aeneas Aeneas.Std Result ProverRwFull
variable [ExternalTypes] [ExternalFuns]

theorem complete
    (public1 : aspis_statement.pool_v1.pair_forest_semantic_terminal.r0.Public)
    (variant : transport.Variant)
    (hash : Slice (Slice U8) → Result (Array U8 32#usize))
    (backend : prover.Backend)
    (sem : host_semantic.BuiltSemantics aspis_core.digest.LegacyHashFn)
    (salts : aspis_prover.state_only_entropy.ReservedStateOnlyAttemptSecrets ×
      aspis_core.state_only_hiding.StateOnlyHidingContext)
    (proof : alloc.vec.Vec U8)
    (success : prover.prove_from_semantics public1 variant hash backend sem salts=ok (.Ok proof)) :
    ∃ (prepared : prover.PreparedOpening) (privateSalts : host_commitment.PrivateSalts)
      (publication : prover.Publication),
      prover.prepare_opening variant hash backend sem=ok (.Ok prepared) ∧
      prover.derive_private_salts salts.1 salts.2 hash 114#u8=ok (.Ok privateSalts) ∧
      prover.finish_opening variant hash prepared privateSalts=ok (.Ok publication) ∧
      prover.publish_compact variant publication=ok (.Ok proof) := by
  unfold prover.prove_from_semantics at success
  obtain ⟨r,hr,h⟩ := PV_RunJoin_ResultPost.bind_eq_ok success
  cases r with
  | Err e => cases h
  | Ok prepared =>
    simp only [core.result.Result.Insts.CoreOpsTry.branch,bind_tc_ok] at h
    obtain ⟨r,hs,h⟩ := PV_RunJoin_ResultPost.bind_eq_ok h
    cases r with
    | Err e => cases h
    | Ok privateSalts =>
      simp only [core.result.Result.Insts.CoreOpsTry.branch,bind_tc_ok] at h
      obtain ⟨r,hf,h⟩ := PV_RunJoin_ResultPost.bind_eq_ok h
      cases r with
      | Err e => cases h
      | Ok publication =>
        simp only [core.result.Result.Insts.CoreOpsTry.branch,bind_tc_ok] at h
        exact ⟨prepared,privateSalts,publication,hr,hs,hf,h⟩
#print axioms complete
end R1Z.PV_RunJoin_PublishReach54
