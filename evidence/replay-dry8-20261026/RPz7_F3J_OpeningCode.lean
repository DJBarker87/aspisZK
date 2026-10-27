import RPz7_F3J_OpeningFacts
set_option autoImplicit false
noncomputable section
namespace AspisR1.F3J_OpeningCode
open Aeneas Aeneas.Std Result
open AspisR1PublicPreparation PreparedHashCode

theorem block {Hash : Type} {D : aspis_core.Digest32 Hash}
    {before after : transcript.Transcript Hash} {row : U8} {payload : Slice U8}
    {value : Array U8 32#usize} (c : F3J_OpeningFacts.Calls D before after row payload value) :
    observe (run (PreparedHashEffects.block effects D before row payload)).1=F3J_OpeningFacts.log c := by
  have ha := c.absorb
  have hb := c.squeeze
  have hs := c.advance
  unfold CallerStep.openingAbsorbParts at ha
  unfold TranscriptStep.readParts at hb hs
  simp only [PreparedHashEffects.block,PreparedHashEffects.absorb,Bind.bind,Pure.pure,
    PreparedHashCode.bind,run,lift,liftM,MonadLift.monadLift,MonadLiftT.monadLift,effects,
    c.tag_add,ha,hb,hs,observe,List.flatMap_cons,List.flatMap_nil,List.singleton_append,
    F3J_OpeningFacts.log]
  rfl

#print axioms block
end AspisR1.F3J_OpeningCode
end
