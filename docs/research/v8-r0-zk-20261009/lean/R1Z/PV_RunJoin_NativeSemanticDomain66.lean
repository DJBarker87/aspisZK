import R1Z.PV_RunJoin_NativeActual63
import R1Z.PV_RunJoin_ProducedOrigin61
import R1Z.PV_RunJoin_SemanticMaterialDomain66
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_NativeSemanticDomain66
open Aeneas Aeneas.Std Result ProverRwFull PV_RunJoin_NativeResidual63

theorem complete {S F : Type} (base : ExternalTypes) (heap : PV_RunJoin_WeightInstalled46.Heap)
    (box : PV_RunJoin_WeightInstalled46.Box) (ops : @ExternalFuns (types base))
    (runtime : @PV_RunJoin_AllocatorWorld63.Runtime (types base) S F)
    (world : PV_FXM_ReserveWorld.World S F) :
    letI : ExternalTypes := types base
    letI : ExternalFuns := opsNative base heap box ops runtime world
    ∀ p : PV_RunJoin_NativeActual63.P base heap box ops runtime world,
      p.val.sem.bytes.length=13831 ∧ ∃ records, PV_RunJoin_SemanticDomain40.Domain
        (opsNative base heap box ops runtime world) (alloc.vec.Vec.deref p.val.sem.bytes)
        27#u8 32#usize 0#u8 records := by
  letI : ExternalTypes := types base
  letI : ExternalFuns := opsNative base heap box ops runtime world
  intro p
  obtain ⟨_,compiled,noised,maskOnly,d,g,padding,initial,hlen,built⟩ :=
    PV_RunJoin_ProducedOrigin61.origin (PV_RunJoin_NativeResidual62.baseTypes base) heap box (residual base ops runtime world) p.val p.property
  have h := PV_RunJoin_SemanticMaterialDomain66.complete
    (PV_RunJoin_NativeResidual62.baseTypes base) heap box (residual base ops runtime world)
    aspis_core.digest.LegacyHashFn.Insts.Aspis_coreDigestDigest32
    prover.Backend.Insts.Aspis_r1_cost_probeHost_semanticCommitments p.val.public1 compiled noised
    maskOnly d g padding initial p.val.hash .S2
  erw [built] at h
  exact h
#print axioms complete
end R1Z.PV_RunJoin_NativeSemanticDomain66
