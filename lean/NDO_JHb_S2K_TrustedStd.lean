import NDO_JHb_S2K_ResultEvent

/-! D157 pure slice-copy semantics. The surrounding carrier contains everything
outside the exclusively borrowed destination (including source bytes). This
explicit named library assumption is not a theorem about the native SDK or a
whole successful child. Valid typed slice provenance is a separate runtime port. -/
set_option autoImplicit false
open Aeneas Aeneas.Std Result
namespace AspisR1.S2K.StdCopy

inductive Outcome (Frame : Type) where
  | returned : List U8 → Frame → Outcome Frame
  | panicked : List U8 → Frame → Outcome Frame

def model {Frame : Type} (dst src : List U8) (frame : Frame) : Outcome Frame :=
  if dst.length = src.length then .returned src frame else .panicked dst frame

/-- The only new TrustedStd field: exact copy or length-mismatch panic;
all state outside the destination is preserved, including on mismatch. -/
structure TrustedStd {Frame : Type}
    (copy : List U8 → List U8 → Frame → Outcome Frame) : Prop where
  slice_copy_from_slice : ∀ dst src frame, copy dst src frame = model dst src frame

theorem consistent {Frame : Type} : TrustedStd (@model Frame) := ⟨by intros; rfl⟩

theorem equal_lengths {Frame : Type}
    (copy : List U8 → List U8 → Frame → Outcome Frame) (std : TrustedStd copy)
    (dst src : List U8) (frame : Frame) (equal : dst.length = src.length) :
    copy dst src frame = .returned src frame := by
  rw [std.slice_copy_from_slice]; exact if_pos equal

theorem different_lengths {Frame : Type}
    (copy : List U8 → List U8 → Frame → Outcome Frame) (std : TrustedStd copy)
    (dst src : List U8) (frame : Frame) (different : dst.length ≠ src.length) :
    copy dst src frame = .panicked dst frame := by
  rw [std.slice_copy_from_slice]; exact if_neg different

#print axioms consistent
#print axioms equal_lengths
#print axioms different_lengths
end AspisR1.S2K.StdCopy
