import NHZ_NativeAssociation
set_option autoImplicit false
noncomputable section
namespace AspisR1.NHZ_DRIVER
open Aeneas Aeneas.Std Result CheckpointBytes5Effect

/-- A checkable obstruction to using a callee's Result equality as its event
packet: one extra successful attempted read leaves the Result unchanged. -/
theorem result_equality_does_not_identify_events
    (parts : SdkC_Source.Parts) (reply : SdkC_Source.Digest) :
    let hashv : SdkC_Source.Parts → Result SdkC_Source.Digest := fun _ => .ok reply
    let pureCode : Code Unit := .done ()
    let readCode : Code Unit := .read parts (fun _ => .done ())
    (SdkC_Source.run hashv pureCode []).1 = (SdkC_Source.run hashv readCode []).1 ∧
    (SdkC_Source.run hashv pureCode []).2 ≠ (SdkC_Source.run hashv readCode []).2 := by
  constructor
  · rfl
  · intro same
    have count := congrArg List.length same
    change 0 = 1 at count
    exact Nat.zero_ne_one count

/-- Duplicate occurrences cannot be replaced by one occurrence even when every
reply and the terminal value agree. This is only a log-shape counterexample,
not a claim of a mismatch in the adopted verifier. -/
theorem duplicate_read_is_charged
    (parts : SdkC_Source.Parts) (reply : SdkC_Source.Digest) :
    let hashv : SdkC_Source.Parts → Result SdkC_Source.Digest := fun _ => .ok reply
    let code : Code Unit := .read parts (fun _ => .read parts (fun _ => .done ()))
    (SdkC_Source.run hashv code []).2.length = 2 := rfl

#print axioms result_equality_does_not_identify_events
#print axioms duplicate_read_is_charged
end AspisR1.NHZ_DRIVER
