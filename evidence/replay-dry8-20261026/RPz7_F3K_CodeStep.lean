import RPz7_F3K_AbsorbCode
import RPz7_AuS1_Trace
set_option autoImplicit false
noncomputable section
namespace AspisR1.F3K_CodeStep
open Aeneas Aeneas.Std Result
open AspisR1PublicPreparation PreparedHashCode
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep AspisV8R19.SqueezeOracleBridge

theorem lift_success {A B : Type} (r : Result A) (v : A) (h : r=ok v) (k : A → Code B) :
    observe (run (PreparedHashCode.bind (monadLift r) k)).1=observe (run (k v)).1 := by
  rw [h]
  rfl

theorem pure_step {A B : Type} (v : A) (k : A → Code B) :
    observe (run (PreparedHashCode.bind (monadLift (ok v : Result A)) k)).1=observe (run (k v)).1 := rfl

theorem digest_success {A Hash : Type} (D : aspis_core.Digest32 Hash) (hash : Hash)
    (parts : Slice (Slice U8)) (value : Array U8 32#usize)
    (h : D.digest hash parts=ok value) (k : Array U8 32#usize → Code A) :
    observe (run (PreparedHashCode.bind (effects.digest D hash parts) k)).1=
      (flatten parts,decodeState value)::observe (run (k value)).1 := by
  simp only [effects,PreparedHashCode.bind,run,h,observe,List.flatMap_cons,List.singleton_append]

theorem absorb {A Hash : Type} (D : aspis_core.Digest32 Hash)
    (before absorbed : transcript.Transcript Hash) (payload : Slice U8)
    (success : transcript.Transcript.absorb D before 31#u8 payload=ok absorbed)
    (k : transcript.Transcript Hash → Code A) :
    observe (run (PreparedHashCode.bind (PreparedHashEffects.absorb effects D before 31#u8 payload) k)).1=
      (flatten (CallerStep.openingAbsorbParts before.state 191#u8
        (UScalar.cast .U32 (Slice.len payload)) payload),decodeState absorbed.state)::
      observe (run (k absorbed)).1 := by
  rw [AuS1_Trace.run_bind,F3K_AbsorbCode.run_absorb D before absorbed payload success]
  rfl

#print axioms lift_success
#print axioms pure_step
#print axioms digest_success
#print axioms absorb
end AspisR1.F3K_CodeStep
end
