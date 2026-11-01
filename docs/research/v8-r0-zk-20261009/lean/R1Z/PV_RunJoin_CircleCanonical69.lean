import R1Z.PV_RunJoin_NativeResidual62
import R1Z.PV_RunJoin_NativeFrames62
import R1Z.PV_RunJoin_CircleInstalledTotal55
import R1Z.PV_RunJoin_ResultPost41
import R1Z.PV_RunJoin_NativeOrigin62
import R1Z.PV_RunJoin_TwoPointFields51
import R1Z.PV_RunJoin_MaterialAlphaProduced51
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_CircleCanonical69
open Aeneas Aeneas.Std Result ProverRwFull PV_RunJoin_NativeResidual62
open ProverCommitSubfieldOps47
attribute [local irreducible] R0P.SemSource.circleSample0 R0P.SemSource.circleSample1
  AspisV8R19.SqueezeOracleBridge.decodeState

theorem complete (base : ExternalTypes) (heap : PV_RunJoin_WeightInstalled46.Heap)
    (box : PV_RunJoin_WeightInstalled46.Box) (ops : @ExternalFuns (types base))
    (block : Array U8 32#usize) (row : aspis_core.r0_transcript.CircleRow) :
    ∃ p,
      @sampler.circle_sample (types base) (opsNative base heap box ops) block row=ok p ∧
      Canonical (PV_RunJoin_SemanticScalar50.raw p.x) ∧
      Canonical (PV_RunJoin_SemanticScalar50.raw p.y) := by
  letI : ExternalTypes := types base
  letI : ExternalFuns := opsNative base heap box ops
  obtain ⟨p,hp,hx,hy,hc⟩ := PV_RunJoin_CircleInstalledTotal55.complete
    (baseTypes base) heap box (beforeCircle base ops) block row
  have nativeCall : @sampler.circle_sample (types base) (opsNative base heap box ops) block row=ok p := by
    change @ExternalFuns.op259 (types base) (opsNative base heap box ops) block row=ok p
    rw [PV_RunJoin_NativeFrames62.op259]
    change @ExternalFuns.op259 (types base)
      (PV_RunJoin_CircleNeutralSelected52.selected (beforeCircle base ops)) block row=ok p
    change @ExternalFuns.op259 (types base)
      (PV_RunJoin_WeightInstalled46.selected (baseTypes base) heap box
        (PV_RunJoin_CircleNeutralSelected52.selected (beforeCircle base ops))) block row=ok p at hp
    rw [PV_RunJoin_CircleInstalled52.installed_projection] at hp
    exact hp
  exact ⟨p,nativeCall,hx,hy⟩

open PV_RunJoin_ResultPost41

def Good (p : aspis_core.circle.SecureCirclePoint) : Prop :=
  Canonical (PV_RunJoin_SemanticScalar50.raw p.x) ∧
    Canonical (PV_RunJoin_SemanticScalar50.raw p.y)

theorem challenge (base : ExternalTypes) (heap : PV_RunJoin_WeightInstalled46.Heap)
    (box : PV_RunJoin_WeightInstalled46.Box) (ops : @ExternalFuns (types base))
    {H : Type} (D : aspis_core.digest.Digest32 H) (t : host_wire.SemanticTranscript H)
    (tag : U8) (framed : Slice U8) :
    Post (fun pair => match pair.1 with | .Err _ => True | .Ok p => Good p)
      (@host_wire.SemanticTranscript.challenge_reference_circle_point (types base)
        (opsNative base heap box ops) H D t tag framed) := by
  letI : ExternalTypes := types base
  letI : ExternalFuns := opsNative base heap box ops
  unfold host_wire.SemanticTranscript.challenge_reference_circle_point
  split
  all_goals first
  | trivial
  | (apply PV_RunJoin_ResultPost41.bind
     rintro ⟨status,next⟩
     dsimp only [Aeneas.Std.uncurry]
     cases status with
     | Err e => trivial
     | Ok block =>
       simp only [core.result.Result.Insts.CoreOpsTry.branch,bind_tc_ok]
       obtain ⟨p,hp,hx,hy⟩ := complete base heap box ops block _
       rw [hp]
       exact ⟨hx,hy⟩)

theorem data (base : ExternalTypes) (heap : PV_RunJoin_WeightInstalled46.Heap)
    (box : PV_RunJoin_WeightInstalled46.Box) (ops : @ExternalFuns (types base))
    (p : PV_RunJoin_NativeActual62.P base heap box ops) :
    letI : ExternalTypes := types base
    letI : ExternalFuns := opsNative base heap box ops
    (∀ i,i<10 → Canonical ((PV_RunJoin_ActualRun.data p.val).p i)) ∧
      Canonical (PV_RunJoin_ActualRun.data p.val).x0 ∧
      Canonical (PV_RunJoin_ActualRun.data p.val).y0 ∧
      Canonical (PV_RunJoin_ActualRun.data p.val).x1 ∧
      Canonical (PV_RunJoin_ActualRun.data p.val).y1 := by
  letI : ExternalTypes := types base
  letI : ExternalFuns := opsNative base heap box ops
  obtain ⟨before,middle,z0,z1,f25,f26,h25,h26,hz⟩ :=
    PV_RunJoin_NativeOrigin62.circles base heap box ops p.val p.property
  have h0 := challenge base heap box ops
    aspis_core.digest.LegacyHashFn.Insts.Aspis_coreDigestDigest32 before 25#u8 f25
  have h1 := challenge base heap box ops
    aspis_core.digest.LegacyHashFn.Insts.Aspis_coreDigestDigest32 middle 26#u8 f26
  rw [h25] at h0
  rw [h26] at h1
  obtain ⟨hx0,hy0,hx1,hy1⟩ := PV_RunJoin_TwoPointFields51.raw p.val.sem z0 z1 hz
  refine ⟨?_,?_,?_,?_,?_⟩
  · obtain ⟨_,compiled,noised,maskOnly,d,g,padding,initial,_,built⟩ :=
      PV_RunJoin_NativeOrigin62.origin base heap box ops p.val p.property
    exact PV_RunJoin_MaterialAlphaProduced51.complete (baseTypes base) heap box (residual base ops)
      aspis_core.digest.LegacyHashFn.Insts.Aspis_coreDigestDigest32
      prover.Backend.Insts.Aspis_r1_cost_probeHost_semanticCommitments p.val.public1 compiled noised
      maskOnly d g padding initial p.val.backend p.val.hash .S2 p.val.sem built
  · change Canonical (PV_RunJoin_SemanticMaterialInputs50.x0 p.val.sem)
    rw [hx0];exact h0.1
  · change Canonical (PV_RunJoin_SemanticMaterialInputs50.y0 p.val.sem)
    rw [hy0];exact h0.2
  · change Canonical (PV_RunJoin_SemanticMaterialInputs50.x1 p.val.sem)
    rw [hx1];exact h1.1
  · change Canonical (PV_RunJoin_SemanticMaterialInputs50.y1 p.val.sem)
    rw [hy1];exact h1.2

#print axioms complete
#print axioms Good
#print axioms challenge
#print axioms data
end R1Z.PV_RunJoin_CircleCanonical69
