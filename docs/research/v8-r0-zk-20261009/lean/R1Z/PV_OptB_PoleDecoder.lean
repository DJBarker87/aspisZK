import R1Z.PV_OptB_FixturePoleDifference
set_option autoImplicit false
namespace R1Z.PV_OptB_PoleDecoder

/-- Generic decoder obstruction. The admitted pole-pair theorem provides
opposite verdicts. This rule by itself supplies no native retry outcomes. -/
theorem no_decoder_of_opposite {W Public Challenge : Type}
    (pub : W → Public) (verdict : W → Challenge → Prop)
    (w u : W) (c : Challenge) (same : pub w = pub u)
    (opposite : verdict w c ↔ ¬ verdict u c) :
    ¬ ∃ decoder : Public → Challenge → Prop,
      ∀ w c, verdict w c ↔ decoder (pub w) c := by
  rintro ⟨decoder,law⟩
  have right := law u c
  rw [← same] at right
  have equivalent := (law w c).trans right.symm
  tauto

#print axioms no_decoder_of_opposite
end R1Z.PV_OptB_PoleDecoder
