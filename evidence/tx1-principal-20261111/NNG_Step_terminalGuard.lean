import NNG_SourceSuffixes
set_option autoImplicit false
noncomputable section
namespace AspisR1.NNG_SourceSuffixes
open Aeneas Aeneas.Std Result NNG_verify_finish NNG_Emitted

/-- Fresh source occurrence 18: SAME typed values and complete Result continuation. Support until concrete child installation. -/
theorem occurrence_terminalGuard {H W : Type} (c : Calls) (s : Parent H W) (alpha : Alpha) (transcript1 : r1_wire.SemanticTranscript H) (val1 : Claims) (val3 : K29) (b : Bool) (r4 : core.result.Result r1_wire.ValidatedRecord r1_wire.Error) :
 f_terminalGuard c s alpha transcript1 val1 val3 b r4 = (do
    let aspis_coredigestDigest32Inst := s.digest
    let public1 := s.publicValue
    let prefix1 := s.prefixValue
    let transcript := s.transcript
    let challenges := s.challenges
    let obs := s.observer
    if b
    then ok (core.result.Result.Err r1_wire.Error.Terminal)
    else
      f_mark4 c s alpha transcript1 val1 val3 r4) := rfl
#print axioms occurrence_terminalGuard
end AspisR1.NNG_SourceSuffixes
