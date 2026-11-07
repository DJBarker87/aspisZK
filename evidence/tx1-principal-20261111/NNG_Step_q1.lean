import NNG_SourceSuffixes
set_option autoImplicit false
noncomputable section
namespace AspisR1.NNG_SourceSuffixes
open Aeneas Aeneas.Std Result NNG_verify_finish NNG_Emitted

/-- Fresh source occurrence 13: SAME typed values and complete Result continuation. Support until concrete child installation. -/
theorem occurrence_q1 {H W : Type} (c : Calls) (s : Parent H W) (running : Q) (val2 : Q) (mask : Q) (alpha : Alpha) (transcript1 : r1_wire.SemanticTranscript H) (val1 : Claims) (val3 : K29) (r4 : core.result.Result r1_wire.ValidatedRecord r1_wire.Error) :
 f_q1 c s running val2 mask alpha transcript1 val1 val3 r4 = (do
    let aspis_coredigestDigest32Inst := s.digest
    let public1 := s.publicValue
    let prefix1 := s.prefixValue
    let transcript := s.transcript
    let challenges := s.challenges
    let obs := s.observer
    let q1 ← c.c5 challenges.eta val2
    f_q2 c s running mask q1 alpha transcript1 val1 val3 r4) := rfl
#print axioms occurrence_q1
end AspisR1.NNG_SourceSuffixes
