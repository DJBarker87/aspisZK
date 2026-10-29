import R1Z.PV_RunJoin_PrepareBatchContext50
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_PrepareBatchCongruence50
open Aeneas Aeneas.Std Result ProverRwFull
variable [ExternalTypes] [ExternalFuns]

theorem complete
  (variant : transport.Variant)
  (hash : Slice (Slice Std.U8) → Result (Array Std.U8 32#usize))
  (backend : prover.Backend)
  (sem : host_semantic.BuiltSemantics aspis_core.digest.LegacyHashFn)
  (coefficients : alloc.vec.Vec (Array aspis_core.field.wide_exact.WideExact 1024#usize))
  (constructor : Result (core.result.Result weights.Weights verifier.Error))
  (materialize : weights.Weights → aspis_core.field.wide_exact.WideExact →
    Result (core.result.Result (alloc.vec.Vec aspis_core.field.wide_exact.WideExact) verifier.Error))
  (claim : Slice (Array aspis_core.field.wide_exact.WideExact 1024#usize) →
    aspis_core.r0.domain.Point aspis_core.field.wide_exact.WideExact → Result (alloc.vec.Vec U8))
  (inactiveValue : Slice aspis_core.field.wide_exact.WideExact → weights.Weights →
    Result aspis_core.field.wide_exact.WideExact)
  (tail : host_transcript.Transcript aspis_core.digest.LegacyHashFn → alloc.vec.Vec U8 →
    aspis_core.field.wide_exact.WideExact → aspis_core.field.wide_exact.WideExact →
    aspis_core.field.wide_exact.WideExact → Slice aspis_core.field.wide_exact.WideExact →
    Slice aspis_core.field.wide_exact.WideExact → Result (core.result.Result prover.PreparedOpening verifier.Error))
  (scalar : host_transcript.Transcript aspis_core.digest.LegacyHashFn → U8 → Slice U8 → Bool →
    Result (aspis_core.field.wide_exact.WideExact × host_transcript.Transcript aspis_core.digest.LegacyHashFn))
  (batch1 batch2 : Slice (Array aspis_core.field.wide_exact.WideExact 1024#usize) →
    aspis_core.field.wide_exact.WideExact → Result (alloc.vec.Vec aspis_core.field.wide_exact.WideExact))
  (heq : ∀ g,batch1 (alloc.vec.Vec.deref coefficients) g=batch2 (alloc.vec.Vec.deref coefficients) g) :
    PV_RunJoin_PrepareBatchContext50.run variant hash backend sem (ok coefficients) constructor materialize claim inactiveValue tail scalar batch1=
      PV_RunJoin_PrepareBatchContext50.run variant hash backend sem (ok coefficients) constructor materialize claim inactiveValue tail scalar batch2 := by
  simp only [PV_RunJoin_PrepareBatchContext50.run,bind_tc_ok,heq]
#print axioms complete
end R1Z.PV_RunJoin_PrepareBatchCongruence50
