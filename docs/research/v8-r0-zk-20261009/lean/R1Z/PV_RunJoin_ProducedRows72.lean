import R1Z.PV_RunJoin_LiftRows72
import R1Z.PV_RunJoin_ProducedOrigin61
import R1Z.PV_RunJoin_MaterialBackendSized66
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_ProducedRows72
open Aeneas Aeneas.Std Result ProverRwFull PV_RunJoin_WeightInstalled46

theorem selected (base : ExternalTypes) (heap : Heap) (box : Box)
    (ops : @ExternalFuns (types base)) :
    letI : ExternalTypes := types base
    letI : ExternalFuns := PV_RunJoin_WeightInstalled46.selected base heap box ops
    ∀ p,PV_RunJoin_ActualProvenance60.Produced p →
      PV_RunJoin_NativePointClaims72.Rows p.sem.columns := by
  letI : ExternalTypes := types base
  letI : ExternalFuns := PV_RunJoin_WeightInstalled46.selected base heap box ops
  intro p hp
  obtain ⟨_,compiled,noised,maskOnly,d,g,padding,initial,_,built⟩ :=
    PV_RunJoin_ProducedOrigin61.origin base heap box ops p hp
  have traced := PV_RunJoin_MaterialBackendSized66.complete base heap box ops
    aspis_core.digest.LegacyHashFn.Insts.Aspis_coreDigestDigest32
    prover.Backend.Insts.Aspis_r1_cost_probeHost_semanticCommitments p.public1 compiled
    noised maskOnly d g padding initial p.hash .S2
  erw [built] at traced
  obtain ⟨columns,lengths,first,root1,root2,h,hs,_,_,lifted⟩ := traced
  exact PV_RunJoin_LiftRows72.complete base heap box ops columns lengths h hs g d p.sem.columns lifted

theorem native {S F : Type} (base : ExternalTypes)
    (heap : PV_RunJoin_NativeResidual63.Heap) (box : PV_RunJoin_NativeResidual63.Box)
    (ops : @ExternalFuns (PV_RunJoin_NativeResidual63.types base))
    (runtime : @PV_RunJoin_AllocatorWorld63.Runtime (PV_RunJoin_NativeResidual63.types base) S F)
    (world : PV_FXM_ReserveWorld.World S F)
    (p : PV_RunJoin_NativeActual63.P base heap box ops runtime world) :
    PV_RunJoin_NativePointClaims72.Rows p.val.sem.columns :=
  selected (PV_RunJoin_NativeResidual62.baseTypes base) heap box
    (PV_RunJoin_NativeResidual63.residual base ops runtime world) p.val p.property

#print axioms selected
#print axioms native
end R1Z.PV_RunJoin_ProducedRows72
