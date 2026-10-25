import R1SelectedTranscriptParams
import R1FinalSoundness
set_option autoImplicit false
noncomputable section
namespace AspisR1.Par_Parameters
open AspisV8R19.DuplexFrames

/-- The exact parameter object used by the frozen2 transcript, not new values. -/
abbrev deployed := SelectedTranscriptParams.params

theorem address_bound : 34 + deployed.D ≤ SelectedTranscriptParams.L := by
  norm_num [deployed, SelectedTranscriptParams.params, SelectedTranscriptParams.D,
    SelectedTranscriptParams.L]

theorem encoder_bound (m : SelectedTranscriptParams.Message) :
    (deployed.enc m).length ≤ deployed.D := m.property

theorem decoder_inverse (m : SelectedTranscriptParams.Message) :
    deployed.dec (deployed.enc m) = some m := SelectedTranscriptParams.dec_enc m

/-- An explicit inhabitant witnesses that the specialised parameter carrier is inhabited. -/
theorem parameter_nonvacuity :
    ∃ m : SelectedTranscriptParams.Message, deployed.dec (deployed.enc m) = some m :=
  ⟨⟨[], Nat.zero_le _⟩, decoder_inverse _⟩

/-- L151 is inherited from the actual model input's LinearMaps, with no law premise. -/
theorem input_map_add (i : R1FinalSoundness.SourceInputs)
    (x y : Fin 1024 → LiteralTranscript.E) :
    (∀ j : Fin 6, i.data.F j (x + y) = i.data.F j x + i.data.F j y) ∧
    i.data.F0 (x + y) = i.data.F0 x + i.data.F0 y := by
  exact ⟨fun j => (i.data.F j).map_add x y, i.data.F0.map_add x y⟩

/-- L152 uses the same maps and their original scalar field. -/
theorem input_map_smul (i : R1FinalSoundness.SourceInputs)
    (a : LiteralTranscript.E) (x : Fin 1024 → LiteralTranscript.E) :
    (∀ j : Fin 6, i.data.F j (a • x) = a • i.data.F j x) ∧
    i.data.F0 (a • x) = a • i.data.F0 x := by
  exact ⟨fun j => (i.data.F j).map_smul a x, i.data.F0.map_smul a x⟩

#print axioms address_bound
#print axioms encoder_bound
#print axioms decoder_inverse
#print axioms parameter_nonvacuity
#print axioms input_map_add
#print axioms input_map_smul
end AspisR1.Par_Parameters
end
