import NNG_SourceSuffixes
set_option autoImplicit false
noncomputable section
namespace AspisR1.NNG_SourceSuffixes
open Aeneas Aeneas.Std Result NNG_verify_finish NNG_Emitted

/-- Fresh source occurrence 29: SAME typed values and complete Result continuation. Support until concrete child installation. -/
theorem occurrence_r11 {H W : Type} (c : Calls) (s : Parent H W) (alpha : Alpha) (val1 : Claims) (val3 : K29) (state_before_z0 : Array U8 32#usize) (val4 : aspis_core.circle.SecureCirclePoint) (val5 : K29) (transcript3 : r1_wire.SemanticTranscript H) (val6 : aspis_core.circle.SecureCirclePoint) (val7 : Slice U8) :
 f_r11 c s alpha val1 val3 state_before_z0 val4 val5 transcript3 val6 val7 = (do
    let aspis_coredigestDigest32Inst := s.digest
    let public1 := s.publicValue
    let prefix1 := s.prefixValue
    let transcript := s.transcript
    let challenges := s.challenges
    let obs := s.observer
    let r11 ←
      core.array.TryFromArrayCopySlice.try_from
        32#usize core.marker.CopyU8 val7
    f_a3 c s alpha val1 val3 state_before_z0 val4 val5 transcript3 val6 r11) := rfl
#print axioms occurrence_r11
end AspisR1.NNG_SourceSuffixes
