import NNG_SourceSuffixes
set_option autoImplicit false
noncomputable section
namespace AspisR1.NNG_SourceSuffixes
open Aeneas Aeneas.Std Result NNG_verify_finish NNG_Emitted

/-- Fresh source occurrence 30: SAME typed values and complete Result continuation. Support until concrete child installation. -/
theorem occurrence_a3 {H W : Type} (c : Calls) (s : Parent H W) (alpha : Alpha) (val1 : Claims) (val3 : K29) (state_before_z0 : Array U8 32#usize) (val4 : aspis_core.circle.SecureCirclePoint) (val5 : K29) (transcript3 : r1_wire.SemanticTranscript H) (val6 : aspis_core.circle.SecureCirclePoint) (r11 : core.result.Result (Array U8 32#usize) core.array.TryFromSliceError) :
 f_a3 c s alpha val1 val3 state_before_z0 val4 val5 transcript3 val6 r11 = (do
    let aspis_coredigestDigest32Inst := s.digest
    let public1 := s.publicValue
    let prefix1 := s.prefixValue
    let transcript := s.transcript
    let challenges := s.challenges
    let obs := s.observer
    let a3 ←
      core.result.Result.unwrap
        core.fmt.DebugTryFromSliceError r11
    ok (core.result.Result.Ok
      {
        roots :=
          (Array.make 2#usize [
            prefix1.c1_root, a3
            ]),
        challenges,
        alpha,
        claims := val1,
        extra := val3,
        before_z1 := val5,
        state_before_z0,
        z := (Array.make 2#usize [ val4, val6 ]),
        transcript := transcript3
      })) := rfl
#print axioms occurrence_a3
end AspisR1.NNG_SourceSuffixes
