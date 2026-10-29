import R1Z.PV_RunJoin_PrepareClaimHead50
import R1Z.PV_RunJoin_SemanticClaimPoint50
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_PreparePoint50
open Aeneas Aeneas.Std Result ProverRwFull
open PV_RunJoin_WeightInstalled46
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
    let y1 ← claim (alloc.vec.Vec.deref coefficients) (PV_RunJoin_SemanticClaimPoint50.point sem.z)
    continuation coefficients y1

set_option allowUnsafeReducibility true in
attribute [local irreducible] ProverRwP6BoundaryInstall.selected
attribute [local irreducible] selected PV_B2_F_RawNative.selected PV_B2_F_ResourceFamilies.selected

theorem complete (base : ExternalTypes) (heap : Heap) (box : Box) (ops : @ExternalFuns (types base))
  (variant : transport.Variant)
  (hash : Slice (Slice Std.U8) → Result (Array Std.U8 32#usize))
  (backend : prover.Backend)
  (sem : host_semantic.BuiltSemantics aspis_core.digest.LegacyHashFn)
  (coefficient_result : Result (alloc.vec.Vec (Array aspis_core.field.wide_exact.WideExact 1024#usize)))
  (constructor : Result (core.result.Result (@weights.Weights (types base)) verifier.Error))
  (materialize : (@weights.Weights (types base)) → aspis_core.field.wide_exact.WideExact →
    Result (core.result.Result (alloc.vec.Vec aspis_core.field.wide_exact.WideExact) verifier.Error))
  (claim : Slice (Array aspis_core.field.wide_exact.WideExact 1024#usize) →
    aspis_core.r0.domain.Point aspis_core.field.wide_exact.WideExact → Result (alloc.vec.Vec U8))
  (inactiveValue : Slice aspis_core.field.wide_exact.WideExact → (@weights.Weights (types base)) →
    Result aspis_core.field.wide_exact.WideExact)
  (tail : host_transcript.Transcript aspis_core.digest.LegacyHashFn → alloc.vec.Vec U8 →
    aspis_core.field.wide_exact.WideExact → aspis_core.field.wide_exact.WideExact →
    aspis_core.field.wide_exact.WideExact → Slice aspis_core.field.wide_exact.WideExact →
    Slice aspis_core.field.wide_exact.WideExact → Result (core.result.Result prover.PreparedOpening verifier.Error))
  (scalar : host_transcript.Transcript aspis_core.digest.LegacyHashFn → U8 → Slice U8 → Bool →
    Result (aspis_core.field.wide_exact.WideExact × host_transcript.Transcript aspis_core.digest.LegacyHashFn))
  (continuation : alloc.vec.Vec (Array aspis_core.field.wide_exact.WideExact 1024#usize) →
    alloc.vec.Vec U8 → Result (core.result.Result prover.PreparedOpening verifier.Error)) :
    @PV_RunJoin_PrepareClaimHead50.run (types base) (selected base heap box ops) variant hash backend sem coefficient_result constructor materialize claim inactiveValue tail scalar continuation=
      @run (types base) (selected base heap box ops) variant hash backend sem coefficient_result constructor materialize claim inactiveValue tail scalar continuation := by
  letI : ExternalTypes := types base
  letI : ExternalFuns := selected base heap box ops
  unfold PV_RunJoin_PrepareClaimHead50.run run
  apply congrArg (Aeneas.Std.bind _)
  funext b
  cases b with
  | true => rfl
  | false =>
    dsimp only [Bool.false_eq_true,if_false]
    apply congrArg (Aeneas.Std.bind _)
    funext coefficients
    have hp := PV_RunJoin_SemanticClaimPoint50.complete base heap box ops sem.z
    have grouped :
        (do let p ← PV_RunJoin_SemanticClaimPoint50.run base heap box ops sem.z
            let y1 ← claim (alloc.vec.Vec.deref coefficients) p
            continuation coefficients y1)=
          (do let y1 ← claim (alloc.vec.Vec.deref coefficients) (PV_RunJoin_SemanticClaimPoint50.point sem.z)
              continuation coefficients y1) := by rw [hp];rfl
    rw [←grouped]
    simp only [PV_RunJoin_SemanticClaimPoint50.run,bind_assoc,bind_tc_ok]
#print axioms run
#print axioms complete
end R1Z.PV_RunJoin_PreparePoint50
