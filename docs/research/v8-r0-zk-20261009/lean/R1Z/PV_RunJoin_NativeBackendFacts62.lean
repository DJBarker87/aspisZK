import R1Z.PV_RunJoin_NativeOrigin62
import R1Z.PV_RunJoin_MaterialBackendTrace60
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_NativeBackendFacts62
open Aeneas Aeneas.Std Result ProverRwFull PV_RunJoin_NativeResidual62

/-- The actual C1 and C2 caller equations are conclusions. The outstanding
lift_columns cell transport into ActualData is not assumed here. -/
theorem trace (base : ExternalTypes) (heap : PV_RunJoin_WeightInstalled46.Heap)
    (box : PV_RunJoin_WeightInstalled46.Box) (ops : @ExternalFuns (types base)) :
    letI : ExternalTypes := types base
    letI : ExternalFuns := opsNative base heap box ops
    ∀ p : PV_RunJoin_NativeActual62.P base heap box ops,
      ∃ (initial : prover.Backend) (columns : Array (alloc.vec.Vec aspis_core.field.M31) 26#usize)
        (d g : Array aspis_core.field.QM31 1024#usize),
        initial.messages.length=29 ∧
        PV_RunJoin_BackendBuildTrace60.Trace
          prover.Backend.Insts.Aspis_r1_cost_probeHost_semanticCommitments columns d g initial p.val.backend p.val.sem := by
  letI : ExternalTypes := types base
  letI : ExternalFuns := opsNative base heap box ops
  intro p
  obtain ⟨_,compiled,noised,maskOnly,d,g,padding,initial,hlen,built⟩ :=
    PV_RunJoin_NativeOrigin62.origin base heap box ops p.val p.property
  have h := PV_RunJoin_MaterialBackendTrace60.complete (baseTypes base) heap box (residual base ops)
    aspis_core.digest.LegacyHashFn.Insts.Aspis_coreDigestDigest32
    prover.Backend.Insts.Aspis_r1_cost_probeHost_semanticCommitments p.val.public1 compiled noised
    maskOnly d g padding initial p.val.hash .S2
  erw [built] at h
  obtain ⟨columns,h⟩ := h
  exact ⟨initial,columns,d,g,hlen,h⟩

theorem coefficients (base : ExternalTypes) (heap : PV_RunJoin_WeightInstalled46.Heap)
    (box : PV_RunJoin_WeightInstalled46.Box) (ops : @ExternalFuns (types base)) :
    letI : ExternalTypes := types base
    letI : ExternalFuns := opsNative base heap box ops
    ∀ p : PV_RunJoin_NativeActual62.P base heap box ops,
      PV_RunJoin_OpeningImages54.Coefficients (PV_RunJoin_ActualRun.data p.val) := by
  letI : ExternalTypes := types base
  letI : ExternalFuns := opsNative base heap box ops
  intro p
  exact PV_RunJoin_ActualData59.canonical_coefficients p.val

#print axioms trace
#print axioms coefficients
end R1Z.PV_RunJoin_NativeBackendFacts62
