import NNG_SourceSuffixes
set_option autoImplicit false
noncomputable section
namespace AspisR1.NNG_SourceSuffixes
open Aeneas Aeneas.Std Result NNG_verify_finish NNG_Emitted

/-- Fresh source occurrence 27: SAME typed values and complete Result continuation. Support until concrete child installation. -/
theorem occurrence_circleGuard {H W : Type} (c : Calls) (s : Parent H W) (alpha : Alpha) (val1 : Claims) (val3 : K29) (state_before_z0 : Array U8 32#usize) (val4 : aspis_core.circle.SecureCirclePoint) (val5 : K29) (transcript3 : r1_wire.SemanticTranscript H) (val6 : aspis_core.circle.SecureCirclePoint) (b1 : Bool) :
 f_circleGuard c s alpha val1 val3 state_before_z0 val4 val5 transcript3 val6 b1 = (do
    let aspis_coredigestDigest32Inst := s.digest
    let public1 := s.publicValue
    let prefix1 := s.prefixValue
    let transcript := s.transcript
    let challenges := s.challenges
    let obs := s.observer
    if b1
    then
      ok (core.result.Result.Err
        r1_wire.Error.EqualCirclePoints)
    else
      f_r10 c s alpha val1 val3 state_before_z0 val4 val5 transcript3 val6) := rfl
#print axioms occurrence_circleGuard
end AspisR1.NNG_SourceSuffixes
