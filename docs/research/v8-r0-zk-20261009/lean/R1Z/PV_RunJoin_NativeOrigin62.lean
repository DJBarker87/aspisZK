import R1Z.PV_RunJoin_NativeActual62
import R1Z.PV_RunJoin_NativeFrames62
import R1Z.PV_RunJoin_ProducedOrigin61
import R1Z.PV_RunJoin_BuildMaterialBackendLength58
import R1Z.PV_RunJoin_CircleSource61
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_NativeOrigin62
open Aeneas Aeneas.Std Result ProverRwFull PV_RunJoin_NativeResidual62

/-- Discharge the old residual source obligation by the adopted binding. -/
theorem circleSource (base : ExternalTypes) (heap : PV_RunJoin_WeightInstalled46.Heap)
    (box : PV_RunJoin_WeightInstalled46.Box) (ops : @ExternalFuns (types base)) :
    @PV_RunJoin_CircleSource61.Source (types base) (opsNative base heap box ops) := by
  intro block row
  change @ExternalFuns.op259 (types base) (opsNative base heap box ops) block row = _
  rw [PV_RunJoin_NativeFrames62.op259]
  rfl

theorem origin (base : ExternalTypes) (heap : PV_RunJoin_WeightInstalled46.Heap)
    (box : PV_RunJoin_WeightInstalled46.Box) (ops : @ExternalFuns (types base)) :
    letI : ExternalTypes := types base
    letI : ExternalFuns := opsNative base heap box ops
    ∀ p, PV_RunJoin_ActualProvenance60.Produced p → PV_RunJoin_BuildOrigin60.Origin p :=
  PV_RunJoin_ProducedOrigin61.origin (baseTypes base) heap box (residual base ops)

theorem circles (base : ExternalTypes) (heap : PV_RunJoin_WeightInstalled46.Heap)
    (box : PV_RunJoin_WeightInstalled46.Box) (ops : @ExternalFuns (types base)) :
    letI : ExternalTypes := types base
    letI : ExternalFuns := opsNative base heap box ops
    ∀ p, PV_RunJoin_ActualProvenance60.Produced p →
      PV_RunJoin_CircleProduced51.Produced
        aspis_core.digest.LegacyHashFn.Insts.Aspis_coreDigestDigest32 p.sem :=
  PV_RunJoin_ProducedOrigin61.circles (baseTypes base) heap box (residual base ops)

theorem backend_length (base : ExternalTypes) (heap : PV_RunJoin_WeightInstalled46.Heap)
    (box : PV_RunJoin_WeightInstalled46.Box) (ops : @ExternalFuns (types base))
    (p : PV_RunJoin_NativeActual62.P base heap box ops) : p.val.backend.messages.length=29 := by
  letI : ExternalTypes := types base
  letI : ExternalFuns := opsNative base heap box ops
  obtain ⟨_,compiled,noised,maskOnly,d,g,padding,initial,hlen,built⟩ :=
    origin base heap box ops p.val p.property
  have h := PV_RunJoin_BuildMaterialBackendLength58.complete (baseTypes base) heap box
    (residual base ops) aspis_core.digest.LegacyHashFn.Insts.Aspis_coreDigestDigest32
      p.val.public1 compiled noised maskOnly d g padding initial p.val.hash .S2 hlen
  rw [built] at h
  exact h

#print axioms circleSource
#print axioms origin
#print axioms circles
#print axioms backend_length
end R1Z.PV_RunJoin_NativeOrigin62
