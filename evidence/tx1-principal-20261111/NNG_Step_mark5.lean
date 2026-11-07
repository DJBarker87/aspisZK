import NNG_SourceSuffixes
set_option autoImplicit false
noncomputable section
namespace AspisR1.NNG_SourceSuffixes
open Aeneas Aeneas.Std Result NNG_verify_finish NNG_Emitted

/-- Fresh source occurrence 25: SAME typed values and complete Result continuation. Support until concrete child installation. -/
theorem occurrence_mark5 {H W : Type} (c : Calls) (s : Parent H W) (alpha : Alpha) (val1 : Claims) (val3 : K29) (state_before_z0 : Array U8 32#usize) (val4 : aspis_core.circle.SecureCirclePoint) (val5 : K29) (transcript3 : r1_wire.SemanticTranscript H) (val6 : aspis_core.circle.SecureCirclePoint) :
 f_mark5 c s alpha val1 val3 state_before_z0 val4 val5 transcript3 val6 = (do
    let aspis_coredigestDigest32Inst := s.digest
    let public1 := s.publicValue
    let prefix1 := s.prefixValue
    let transcript := s.transcript
    let challenges := s.challenges
    let obs := s.observer
    c.c9 obs 5#u8
    f_b1 c s alpha val1 val3 state_before_z0 val4 val5 transcript3 val6) := rfl
#print axioms occurrence_mark5
end AspisR1.NNG_SourceSuffixes
