import RPz8_CPR_Separation
import S2W_D189Consolidation

set_option autoImplicit false
noncomputable section
namespace AspisR1.CPR_AdmissionGap
open Aeneas Aeneas.Std Result S2Trust S2W_D189Entry

def entry (record : Record) (buffer : Slice U8) : Entry where
  handles := fun _ => (0,1)
  records := fun _ => record
  buffers := fun _ => buffer
  base := fun _ => 0
  provenance := fun _ => 0

theorem valid (record : Record) (buffer : Slice U8) : Valid (entry record buffer).heap := by
  refine ⟨List.Pairwise.nil,?_,?_,?_⟩
  · intro c
    simp [Entry.heap,count,minCounter,maxCounter]
  · intro g member
    cases member
  · intro a live
    exact ⟨by change (0 : Nat) ≠ 1; decide,rfl⟩

theorem admitted (record : Record) (buffer : Slice U8) (count : Nat) :
    S2W_D189Consolidation.RuntimeEntrypointAdmission (model (Nat → Record))
      (entry record buffer) (entry record buffer).heap count where
  entry := {
    valid := valid record buffer
    freshGuards := rfl
    noExternalBorrows := fun _ => rfl
    liveAccount := fun _ _ => rfl
    counterZero := fun _ _ => rfl
    sharedCellsOnlyEqualKeys := fun _ _ _ _ _ => rfl
    duplicateKeysShareCell := fun _ _ _ _ _ => rfl }
  related := rfl

def other : Slice U8 := ⟨83#u8 :: List.replicate 1767 (0#u8),by
  simp only [List.length_cons,List.length_replicate]; scalar_tac⟩

theorem unequal : Hist_Nonvacuity.checkpoint.val ≠ other.val := by
  intro eq
  have head := congrArg (fun xs : List U8 => xs[0]?) eq
  change some (82#u8) = some (83#u8) at head
  exact (by decide : (82#u8) ≠ 83#u8) (Option.some.inj head)

/-- Full SDK model and both exact entry-admission records are inhabited with
identical physical key metadata, equal CP lengths, but unequal buffers. There
is deliberately NO assertion of native verifier acceptance in this model. -/
theorem gap (record : Record) :
    S2TrustedSdkBorrow (model (Nat → Record)) ∧
    Nonempty (S2W_D189Consolidation.RuntimeEntrypointAdmission (model (Nat → Record))
      (entry record Hist_Nonvacuity.checkpoint) (entry record Hist_Nonvacuity.checkpoint).heap 3) ∧
    Nonempty (S2W_D189Consolidation.RuntimeEntrypointAdmission (model (Nat → Record))
      (entry record other) (entry record other).heap 7) ∧
    ((entry record Hist_Nonvacuity.checkpoint).records 0).owned.key =
      ((entry record other).records 0).owned.key ∧
    Hist_Nonvacuity.checkpoint.val.length = other.val.length ∧
    Hist_Nonvacuity.checkpoint.val ≠ other.val :=
  ⟨model_satisfies _,⟨admitted record _ 3⟩,⟨admitted record _ 7⟩,rfl,rfl,unequal⟩

#print axioms valid
#print axioms admitted
#print axioms unequal
#print axioms gap
end AspisR1.CPR_AdmissionGap
end
