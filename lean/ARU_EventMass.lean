import ARU_EventInclusion
set_option autoImplicit false
noncomputable section
namespace AspisR1.ARU_EventMass
open Aeneas Aeneas.Std Result SdkC_Source
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw P6C_EventTransport
open scoped BigOperators
attribute [local instance] Classical.propDecidable
theorem mass {I A : Type} (worlds : Finset I) (weight : I → Rat)
    (nonnegative : ∀ i ∈ worlds, 0 ≤ weight i)
    (hashv : I → Parts → Result Digest) (H : I → Bytes → State)
    (code : I → Code A) (bad : List (Bytes × State) → A → Prop)
    (agrees : ∀ i, ARS_QueryTransport.Agrees (H i) (run (hashv i) (code i) []).2) :
    (∑ i ∈ worlds, if realEvent (hashv i) (code i) bad then weight i else 0) ≤
      ∑ i ∈ worlds, if idealEvent (H i) (code i) bad then weight i else 0 := by
  classical
  apply Finset.sum_le_sum
  intro i member
  by_cases occurs : realEvent (hashv i) (code i) bad
  · have ideal := ARU_EventInclusion.inclusion (hashv i) (H i) (code i) bad (agrees i) occurs
    simp only [if_pos occurs,if_pos ideal,le_refl]
  · simp only [if_neg occurs]
    split
    · exact nonnegative i member
    · exact le_refl _

#print axioms mass
end AspisR1.ARU_EventMass
end
