import R1Z.PV_RunJoin_NativeOrigin62
import R1Z.PV_RunJoin_CircleChallenge62
import R1Z.PV_RunJoin_ActualSample60
import R1Z.PV_RunJoin_ActualPreparedCanonical60
import R1Z.PV_RunJoin_ActualAlpha1Canonical60
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_NativeSample62
open Aeneas Aeneas.Std Result ProverRwFull PV_RunJoin_NativeResidual62
open ProverCommitSubfieldOps47

theorem point_facts (base : ExternalTypes) (heap : PV_RunJoin_WeightInstalled46.Heap)
    (box : PV_RunJoin_WeightInstalled46.Box) (ops : @ExternalFuns (types base))
    (p : PV_RunJoin_NativeActual62.P base heap box ops) :
    letI : ExternalTypes := types base
    ∃ z0 z1, p.val.sem.z=Array.make 2#usize [z0,z1] ∧
      PV_RunJoin_CircleChallenge62.Good z0 ∧ PV_RunJoin_CircleChallenge62.Good z1 := by
  letI : ExternalTypes := types base
  letI : ExternalFuns := opsNative base heap box ops
  obtain ⟨before,middle,z0,z1,f25,f26,h25,h26,hz⟩ :=
    PV_RunJoin_NativeOrigin62.circles base heap box ops p.val p.property
  have h0 := PV_RunJoin_CircleChallenge62.first base heap box ops
    aspis_core.digest.LegacyHashFn.Insts.Aspis_coreDigestDigest32 before f25
  have h1 := PV_RunJoin_CircleChallenge62.second base heap box ops
    aspis_core.digest.LegacyHashFn.Insts.Aspis_coreDigestDigest32 middle f26
  rw [h25] at h0
  rw [h26] at h1
  exact ⟨z0,z1,hz,h0,h1⟩

theorem sourceFacts (base : ExternalTypes) (heap : PV_RunJoin_WeightInstalled46.Heap)
    (box : PV_RunJoin_WeightInstalled46.Box) (ops : @ExternalFuns (types base))
    (p : PV_RunJoin_NativeActual62.P base heap box ops)
    (prepared : @prover.PreparedOpening (types base))
    (hp : @prover.prepare_opening (types base) (opsNative base heap box ops)
      .S2 p.val.hash p.val.backend p.val.sem=ok (.Ok prepared)) :
    @PV_RunJoin_ActualSample60.SourceFacts (types base) (opsNative base heap box ops) p.val := by
  letI : ExternalTypes := types base
  letI : ExternalFuns := opsNative base heap box ops
  obtain ⟨z0,z1,hz,h0,h1⟩ := point_facts base heap box ops p
  obtain ⟨hx0,hy0,hx1,hy1⟩ := PV_RunJoin_TwoPointFields51.raw p.val.sem z0 z1 hz
  have e0 : PV_RunJoin_ActualCircle60.coordinates p.val 0=
      PV_RunJoin_CircleInstalledExact55.coordinates z0 := by
    unfold PV_RunJoin_ActualCircle60.coordinates
    rw [hz,PV_RunJoin_TwoPointFields51.first]
    rfl
  have e1 : PV_RunJoin_ActualCircle60.coordinates p.val 1=
      PV_RunJoin_CircleInstalledExact55.coordinates z1 := by
    unfold PV_RunJoin_ActualCircle60.coordinates
    rw [hz,PV_RunJoin_TwoPointFields51.second]
    rfl
  obtain ⟨hg,hk,ha⟩ := PV_RunJoin_ActualPreparedCanonical60.complete
    (baseTypes base) heap box (residual base ops) p.val prepared hp
  refine ⟨?_,?_,?_,?_,?_,hg,hk,ha,?_,?_,?_⟩
  · obtain ⟨_,compiled,noised,maskOnly,d,g,padding,initial,_,built⟩ :=
      PV_RunJoin_NativeOrigin62.origin base heap box ops p.val p.property
    exact PV_RunJoin_MaterialAlphaProduced51.complete (baseTypes base) heap box (residual base ops)
      aspis_core.digest.LegacyHashFn.Insts.Aspis_coreDigestDigest32
      prover.Backend.Insts.Aspis_r1_cost_probeHost_semanticCommitments p.val.public1 compiled noised
      maskOnly d g padding initial p.val.backend p.val.hash .S2 p.val.sem built
  · change Canonical (PV_RunJoin_SemanticMaterialInputs50.x0 p.val.sem)
    rw [hx0];exact h0.1
  · change Canonical (PV_RunJoin_SemanticMaterialInputs50.y0 p.val.sem)
    rw [hy0];exact h0.2.1
  · change Canonical (PV_RunJoin_SemanticMaterialInputs50.x1 p.val.sem)
    rw [hx1];exact h1.1
  · change Canonical (PV_RunJoin_SemanticMaterialInputs50.y1 p.val.sem)
    rw [hy1];exact h1.2.1
  · exact PV_RunJoin_ActualAlpha1Canonical60.complete (baseTypes base) heap box (residual base ops) p.val
  · rw [e0];exact h0.2.2
  · rw [e1];exact h1.2.2

theorem common (base : ExternalTypes) (heap : PV_RunJoin_WeightInstalled46.Heap)
    (box : PV_RunJoin_WeightInstalled46.Box) (ops : @ExternalFuns (types base)) :
    @PV_RunJoin_PublishProduced60.PV_RunJoin_Link_CommonSample (types base) (opsNative base heap box ops) := by
  letI : ExternalTypes := types base
  letI : ExternalFuns := opsNative base heap box ops
  intro _ p prepared hp
  have sample := PV_RunJoin_ActualSample60.association p.val (sourceFacts base heap box ops p prepared hp)
  obtain ⟨hg,hk,ha⟩ := PV_RunJoin_ActualScalar60.prepared p.val prepared hp
  exact ⟨sample,rfl,rfl,rfl,rfl,rfl,hg,hk,ha⟩

#print axioms point_facts
#print axioms sourceFacts
#print axioms common
end R1Z.PV_RunJoin_NativeSample62
