import RawK_InitHead
import RawK_ModelHead
set_option autoImplicit false
noncomputable section
namespace AspisR1.LogA_Tags
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep

/-- Only the fixed leading tags; state-prefixed duplex calls and raw proof/pub
hashes are deliberately excluded. This is not global oracle separation. -/
def tags : List Bytes :=
  [PublicInitFrame.domain, OpeningReseedFrame.domain,
   OraclePortPhysicalFrameDraft.domain, [16,113], [16,241], [16,114], [18]]

theorem prefix_free : tags.Pairwise (fun a b => ¬ a.IsPrefix b ∧ ¬ b.IsPrefix a) := by
  decide

/-- Framing adds a fixed prefix injectively. Payload field boundaries still
need their own fixed-width or length-code argument. -/
theorem fixed_prefix_injective (tag : Bytes) : Function.Injective (fun b : Bytes => tag ++ b) := by
  intro a b h
  exact List.append_cancel_left h

/-- Squeeze and advance may be swapped at a common absorbed state without
changing either input. This says nothing about their output distribution. -/
theorem squeeze_advance_separate (s t : State) : squeeze (bytes s) ≠ advance (bytes t) :=
  cross_disjoint _ _

/-- All genuine duplex states have width 32: short calls cannot equal absorbs. -/
theorem short_absorb_separate (s t : State) (label : AspisV8R19.DuplexFrames.Byte) (payload : Bytes) :
    squeeze (bytes s) ≠ absorb (bytes t) label payload ∧
      advance (bytes s) ≠ absorb (bytes t) label payload :=
  absorb_disjoint _ _ (bytes_length s) (bytes_length t) label payload

/-- Literal source semantic domain and model domain coincide, byte for byte. -/
theorem semantic_domain :
    MultiproofConeCanonical.bytesOf AspisR1PublicPreparation.r1_wire.DOMAIN.val =
      PublicInitFrame.domain := by
  unfold AspisR1PublicPreparation.r1_wire.DOMAIN
  rfl

#print axioms prefix_free
#print axioms fixed_prefix_injective
#print axioms squeeze_advance_separate
#print axioms short_absorb_separate
#print axioms semantic_domain
end AspisR1.LogA_Tags
end
