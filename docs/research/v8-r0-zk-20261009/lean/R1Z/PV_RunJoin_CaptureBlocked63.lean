import R1Z.PV_RunJoin_BackendBlocked63
import R1Z.PV_RunJoin_ProducedOrigin61
import R1Z.PV_RunJoin_MaterialBackendTrace60
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_CaptureBlocked63
open Aeneas Aeneas.Std Result ProverRwFull PV_RunJoin_WeightInstalled46

/-- Symbolic necessity of a successful reached worker cone. This diagnostic
is about residual dictionaries, not a failure of the shipped implementation. -/
theorem no_capture (base : ExternalTypes) (heap : Heap) (box : Box)
    (ops : @ExternalFuns (types base))
    (denied : @PV_RunJoin_WorkerObstruction63.Denied (types base) (selected base heap box ops)) :
    letI : ExternalTypes := types base
    letI : ExternalFuns := selected base heap box ops
    ∀ p, ¬PV_RunJoin_ActualProvenance60.Produced p := by
  letI : ExternalTypes := types base
  letI : ExternalFuns := selected base heap box ops
  intro p hp
  obtain ⟨_,compiled,noised,maskOnly,d,g,padding,initial,hlen,built⟩ :=
    PV_RunJoin_ProducedOrigin61.origin base heap box ops p hp
  have traced := PV_RunJoin_MaterialBackendTrace60.complete base heap box ops
    aspis_core.digest.LegacyHashFn.Insts.Aspis_coreDigestDigest32
    prover.Backend.Insts.Aspis_r1_cost_probeHost_semanticCommitments p.public1 compiled
    noised maskOnly d g padding initial p.hash .S2
  erw [built] at traced
  obtain ⟨columns,first,root1,root2,h,hfirst,_⟩ := traced
  have blocked := @PV_RunJoin_BackendBlocked63.c1 (types base) (selected base heap box ops)
    (PV_RunJoin_CaptureBoundary61.selected_mapErr base heap box ops) denied initial columns d
  exact PV_RunJoin_ResultPost41.success _ _ _ blocked hfirst

#print axioms no_capture
end R1Z.PV_RunJoin_CaptureBlocked63
