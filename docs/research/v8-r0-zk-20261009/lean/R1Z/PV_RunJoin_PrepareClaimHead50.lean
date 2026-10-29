import R1Z.PV_RunJoin_PrepareClaimContinuation50
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_PrepareClaimHead50
open Aeneas Aeneas.Std Result ControlFlow Error ProverRwFull
variable [ExternalTypes] [ExternalFuns]

def run
  (variant : transport.Variant)
  (hash : Slice (Slice Std.U8) → Result (Array Std.U8 32#usize))
  (backend : prover.Backend)
  (sem : host_semantic.BuiltSemantics aspis_core.digest.LegacyHashFn)
  (coefficient_result : Result (alloc.vec.Vec (Array aspis_core.field.wide_exact.WideExact 1024#usize)))
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
  (continuation : alloc.vec.Vec (Array aspis_core.field.wide_exact.WideExact 1024#usize) →
    alloc.vec.Vec U8 → Result (core.result.Result prover.PreparedOpening verifier.Error)) :
  Result (core.result.Result prover.PreparedOpening verifier.Error) := do
  let b ←
    core.cmp.PartialEq.ne.trait_default
      transport.Variant.Insts.CoreCmpPartialEqVariant variant
      transport.Variant.S2
  if b
  then ok (core.result.Result.Err verifier.Error.Semantic)
  else
    let s := alloc.vec.Vec.deref backend.messages
    let coefficients ← coefficient_result
    let scp ← Array.index_usize sem.z 1#usize
    let we ← aspis_core.field.wide_exact.WideExact.from_qm31 scp.x
    let we1 ← aspis_core.field.wide_exact.WideExact.from_qm31 scp.y
    let s1 := alloc.vec.Vec.deref coefficients
    let y1 ← claim s1 { x := we, y := we1 }
    continuation coefficients y1

theorem source
  (variant : transport.Variant)
  (hash : Slice (Slice Std.U8) → Result (Array Std.U8 32#usize))
  (backend : prover.Backend)
  (sem : host_semantic.BuiltSemantics aspis_core.digest.LegacyHashFn)
  (coefficient_result : Result (alloc.vec.Vec (Array aspis_core.field.wide_exact.WideExact 1024#usize)))
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
    Result (aspis_core.field.wide_exact.WideExact × host_transcript.Transcript aspis_core.digest.LegacyHashFn)) :
    PV_RunJoin_PrepareScalarContext49.run variant hash backend sem coefficient_result constructor materialize claim inactiveValue tail scalar=
      run variant hash backend sem coefficient_result constructor materialize claim inactiveValue tail scalar
        (PV_RunJoin_PrepareClaimContinuation50.run variant hash backend sem coefficient_result constructor materialize claim inactiveValue tail scalar) := by rfl
#print axioms run
#print axioms source
end R1Z.PV_RunJoin_PrepareClaimHead50
