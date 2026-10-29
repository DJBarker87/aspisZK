import R1Z.PV_RunJoin_PrepareScalarInstalled49
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_PrepareSource49
open Aeneas Aeneas.Std Result ProverRwFull
open PV_RunJoin_WeightInstalled46
set_option allowUnsafeReducibility true in
attribute [local irreducible] ProverRwP6BoundaryInstall.selected
attribute [local irreducible] selected PV_B2_F_RawNative.selected PV_B2_F_ResourceFamilies.selected

theorem complete (base : ExternalTypes) (heap : Heap) (box : Box) (ops : @ExternalFuns (types base))
    (variant : transport.Variant) (hash : Slice (Slice U8) → Result (Array U8 32#usize))
    (backend : prover.Backend) (sem : host_semantic.BuiltSemantics aspis_core.digest.LegacyHashFn) :
    @prover.prepare_opening (types base) (selected base heap box ops) variant hash backend sem=
      @PV_RunJoin_PrepareScalarContext49.run (types base) (selected base heap box ops) variant hash backend sem
        (@prover.opening_coefficients (types base) (selected base heap box ops) variant (alloc.vec.Vec.deref backend.messages))
        (@weights.Weights.new (types base) (selected base heap box ops) variant sem.alpha sem.z)
        (@weights.Weights.materialize (types base) (selected base heap box ops))
        (@prover.opening_claim_bytes (types base) (selected base heap box ops))
        (@prover.opening_inactive (types base) (selected base heap box ops))
        (@PV_RunJoin_PrepareTail48.run (types base) (selected base heap box ops) variant hash backend sem)
        (PV_RunJoin_ScalarSource49.retained base heap box ops
          (@aspis_core.digest.LegacyHashFn.Insts.Aspis_coreDigestDigest32 (types base) (selected base heap box ops))) := by
  letI : ExternalTypes := types base
  letI : ExternalFuns := selected base heap box ops
  rw [PV_RunJoin_PrepareOperations47.source,PV_RunJoin_PrepareClaimContext48.source,
    PV_RunJoin_PrepareMaterialContext49.source]
  exact PV_RunJoin_PrepareScalarInstalled49.complete base heap box ops variant hash backend sem _ _ _ _ _ _
#print axioms complete
end R1Z.PV_RunJoin_PrepareSource49
