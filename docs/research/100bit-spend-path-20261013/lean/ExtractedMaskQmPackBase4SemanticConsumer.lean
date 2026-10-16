import ExtractedMaskQmPackBase4Whole
import ExtractedMaskQmPackBase4Semantic

/-! Concrete consumer: the generated four-element packer computes the existing
`R0P.pack4` model after the concrete exact-to-wide map. -/
set_option autoImplicit false
namespace AspisR1.ExtractedMaskQmPackBase4SemanticConsumer

noncomputable section

open AspisV8R15.ExactTowerBase

abbrev CurrentQM := AspisR1.ExtractedMaskQM31Exact.CurrentQM
abbrev CurrentCanonicalQM := AspisR1.ExtractedMaskQM31Exact.CurrentCanonicalQM
abbrev PackB := AspisR1.ExtractedMaskQmPackBase4Semantic.PackB
abbrev f := AspisR1.ExtractedMaskQmPackBase4Semantic.f

theorem generated_pack_maps_to_pack4
    (values : Aeneas.Std.Slice AspisR1SelectedMaskProbe.field.QM31)
    (hlen : values.length = 4)
    (hcanonical : ∀ j : Fin 4,
      CurrentCanonicalQM (AspisR1.ExtractedMaskQmPackBase4Whole.inputAt values hlen j)) :
    ∃ out : CurrentQM,
      AspisR1SelectedMaskProbe.field.qm31_pack_base4 values = .ok out ∧
      CurrentCanonicalQM out ∧
      f (AspisR1.ExtractedMaskQM31Exact.decode out) =
        R0P.pack4 PackB (fun j =>
          f (AspisR1.ExtractedMaskQM31Exact.decode
            (AspisR1.ExtractedMaskQmPackBase4Whole.inputAt values hlen j))) := by
  obtain ⟨out, hout, hcanonicalOut, hdecode⟩ :=
    AspisR1.ExtractedMaskQmPackBase4Whole.qm31_pack_base4_success
      values hlen hcanonical
  refine ⟨out, hout, hcanonicalOut, ?_⟩
  rw [hdecode]
  exact AspisR1.ExtractedMaskQmPackBase4Semantic.map_mathPack
    (AspisR1.ExtractedMaskQmPackBase4Whole.inputAt values hlen)

#print axioms generated_pack_maps_to_pack4

end
end AspisR1.ExtractedMaskQmPackBase4SemanticConsumer
