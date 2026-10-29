import R1Z.PV_RunJoin_PrepareScalarContext49
import R1Z.PV_RunJoin_ScalarSource49
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_PrepareScalarInstalled49
open Aeneas Aeneas.Std Result ProverRwFull
open PV_RunJoin_WeightInstalled46
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
    Slice aspis_core.field.wide_exact.WideExact → Result (core.result.Result prover.PreparedOpening verifier.Error)) :
    @PV_RunJoin_PrepareMaterialContext49.run (types base) (selected base heap box ops)
      variant hash backend sem coefficient_result constructor materialize claim inactiveValue tail=
    @PV_RunJoin_PrepareScalarContext49.run (types base) (selected base heap box ops)
      variant hash backend sem coefficient_result constructor materialize claim inactiveValue tail
      (PV_RunJoin_ScalarSource49.retained base heap box ops
        (@aspis_core.digest.LegacyHashFn.Insts.Aspis_coreDigestDigest32 (types base) (selected base heap box ops))) := by
  letI : ExternalTypes := types base
  letI : ExternalFuns := selected base heap box ops
  rw [PV_RunJoin_PrepareScalarContext49.source]
  apply congrArg (fun scalar => PV_RunJoin_PrepareScalarContext49.run variant hash backend sem
    coefficient_result constructor materialize claim inactiveValue tail scalar)
  funext tr row payload nonzero
  exact PV_RunJoin_ScalarSource49.complete base heap box ops _ tr row payload nonzero
#print axioms complete
end R1Z.PV_RunJoin_PrepareScalarInstalled49
