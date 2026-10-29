import R1Z.PV_RunJoin_CircleNativeLaws62
import R1Z.PV_RunJoin_ResultPost41
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_CircleChallenge62
open Aeneas Aeneas.Std Result ProverRwFull PV_RunJoin_NativeResidual62
open ProverCommitSubfieldOps47 PV_RunJoin_ResultPost41

def Good (p : aspis_core.circle.SecureCirclePoint) : Prop :=
  Canonical (PV_RunJoin_SemanticScalar50.raw p.x) ∧
  Canonical (PV_RunJoin_SemanticScalar50.raw p.y) ∧
  (PV_RunJoin_CircleInstalledExact55.coordinates p).1^2+
    (PV_RunJoin_CircleInstalledExact55.coordinates p).2^2=1

theorem first (base : ExternalTypes) (heap : PV_RunJoin_WeightInstalled46.Heap)
    (box : PV_RunJoin_WeightInstalled46.Box) (ops : @ExternalFuns (types base))
    {H : Type} (D : aspis_core.digest.Digest32 H) (t : host_wire.SemanticTranscript H)
    (framed : Slice U8) :
    Post (fun pair => match pair.1 with | .Err _ => True | .Ok p => Good p)
      (@host_wire.SemanticTranscript.challenge_reference_circle_point (types base)
        (opsNative base heap box ops) H D t 25#u8 framed) := by
  letI : ExternalTypes := types base
  letI : ExternalFuns := opsNative base heap box ops
  unfold host_wire.SemanticTranscript.challenge_reference_circle_point
  apply PV_RunJoin_ResultPost41.bind
  rintro ⟨status,next⟩
  dsimp only [Aeneas.Std.uncurry]
  cases status with
  | Err e => trivial
  | Ok block =>
    simp only [core.result.Result.Insts.CoreOpsTry.branch,bind_tc_ok]
    obtain ⟨p,hp,hx,hy,hu⟩ := PV_RunJoin_CircleNativeLaws62.complete base heap box ops block .First
    rw [hp]
    exact ⟨hx,hy,hu⟩

#print axioms first

theorem second (base : ExternalTypes) (heap : PV_RunJoin_WeightInstalled46.Heap)
    (box : PV_RunJoin_WeightInstalled46.Box) (ops : @ExternalFuns (types base))
    {H : Type} (D : aspis_core.digest.Digest32 H) (t : host_wire.SemanticTranscript H)
    (framed : Slice U8) :
    Post (fun pair => match pair.1 with | .Err _ => True | .Ok p => Good p)
      (@host_wire.SemanticTranscript.challenge_reference_circle_point (types base)
        (opsNative base heap box ops) H D t 26#u8 framed) := by
  letI : ExternalTypes := types base
  letI : ExternalFuns := opsNative base heap box ops
  unfold host_wire.SemanticTranscript.challenge_reference_circle_point
  apply PV_RunJoin_ResultPost41.bind
  rintro ⟨status,next⟩
  dsimp only [Aeneas.Std.uncurry]
  cases status with
  | Err e => trivial
  | Ok block =>
    simp only [core.result.Result.Insts.CoreOpsTry.branch,bind_tc_ok]
    obtain ⟨p,hp,hx,hy,hu⟩ := PV_RunJoin_CircleNativeLaws62.complete base heap box ops block .Second
    rw [hp]
    exact ⟨hx,hy,hu⟩

#print axioms second

#print axioms Good
end R1Z.PV_RunJoin_CircleChallenge62
