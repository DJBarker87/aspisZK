import LIB_VResult
set_option autoImplicit false
noncomputable section
namespace LIB_VCode
open Aeneas Aeneas.Std LIB_VCarriers
open AspisR1PublicPreparation
def digest (env : RSL.Env) : aspis_core.Digest32 Unit :=
 ⟨⟨⟨fun _ => .ok (),fun _ _ => .ok ()⟩⟩,fun _ parts => LIB_Env.hashv env parts⟩
def event (env : RSL.Env) : PreparedHashCode.Event → RSL.Event
 | .digest _ _ parts _ =>
   let input := NNC_ResumeEvents.parts parts
   .digest input (env.sha256 input)
def events (env : RSL.Env) (log : PreparedHashCode.Log) : List RSL.Event :=
 log.map (event env)
def obs {A B : Type} (env : RSL.Env) (f : A→B)
 (run : PreparedHashCode.Log × Result A) : RSL.Obs B :=
 LIB_Carriers.resultObs f (events env run.1) run.2
def law {A B : Type} (f : A→B)
 (code : RSL.Env→PreparedHashCode.Code A) : RSL.Spec B :=
 fun env o => o=obs env f (PreparedHashCode.run (code env))
theorem digest_exact (env : RSL.Env) (parts : Slice (Slice U8)) :
 (digest env).digest () parts = .ok (LIB_Env.nativeKey (env.sha256 (NNC_ResumeEvents.parts parts))) := rfl
theorem law_exact {A B : Type} (f : A→B) (code : RSL.Env→PreparedHashCode.Code A)
 (env : RSL.Env) (o : RSL.Obs B) : law f code env o ↔
 o=obs env f (PreparedHashCode.run (code env)) := Iff.rfl
theorem functional {A B : Type} (f : A→B) (code : RSL.Env→PreparedHashCode.Code A) :
 RSL.Spec.Functional (law f code) := fun env => ⟨_,fun _=>Iff.rfl⟩
#print axioms digest_exact
#print axioms law_exact
#print axioms functional
end LIB_VCode
