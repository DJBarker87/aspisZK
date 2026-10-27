import R1Z.ProverRwFullFuns
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_Join_PublicPrefix5
open Aeneas Aeneas.Std Result ProverRwFull
variable [ExternalTypes]
abbrev Public := aspis_statement.pool_v1.pair_forest_semantic_terminal.r0.Public
abbrev Compiled := aspis_statement.pool_v1.pair_forest_trace.PoolV1PairForestMergedC1CompilationV1
abbrev Secrets := aspis_prover.state_only_entropy.StateOnlyAttemptSecrets
abbrev Store := aspis_prover.state_only_entropy.DurableStateOnlyMaskNonceStore
abbrev BytesReply := core.result.Result (alloc.vec.Vec U8) aspis_core.state_only_prefix.r0.Error
abbrev AttemptReply := Result ((core.result.Result ((alloc.vec.Vec U8) × prover.MaskedFixtureAudit) verifier.Error) × Store)

/-- Exact first bind in the extracted attempt. This identifies the first
operation when an attempt is entered, not reachability through retry admission. -/
theorem first (ops : ExternalFuns) (pub : Public) (compiled : Compiled)
    (v : transport.Variant) (hash : Slice (Slice U8) → Result (Array U8 32#usize))
    (attempt : Secrets) (store : Store) :
    ∃ next : BytesReply → AttemptReply,
      @prover.prove_masked_attempt _ ops pub compiled v hash attempt store = (ops.op226 pub >>= next) := by
  unfold prover.prove_masked_attempt
  exact ⟨_,rfl⟩

theorem abort (ops : ExternalFuns) (pub : Public) (compiled : Compiled)
    (v : transport.Variant) (hash : Slice (Slice U8) → Result (Array U8 32#usize))
    (attempt : Secrets) (store : Store) (e : Error) (h : ops.op226 pub = .fail e) :
    @prover.prove_masked_attempt _ ops pub compiled v hash attempt store = .fail e := by
  obtain ⟨next,hn⟩ := first ops pub compiled v hash attempt store
  rw [hn,h]
  rfl

theorem diverge (ops : ExternalFuns) (pub : Public) (compiled : Compiled)
    (v : transport.Variant) (hash : Slice (Slice U8) → Result (Array U8 32#usize))
    (attempt : Secrets) (store : Store) (h : ops.op226 pub = .div) :
    @prover.prove_masked_attempt _ ops pub compiled v hash attempt store = .div := by
  obtain ⟨next,hn⟩ := first ops pub compiled v hash attempt store
  rw [hn,h]
  rfl

#print axioms first
#print axioms abort
#print axioms diverge
end R1Z.PV_Join_PublicPrefix5
