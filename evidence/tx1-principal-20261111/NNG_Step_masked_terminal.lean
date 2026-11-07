import NNG_SourceSuffixes
set_option autoImplicit false
noncomputable section
namespace AspisR1.NNG_SourceSuffixes
open Aeneas Aeneas.Std Result NNG_verify_finish NNG_Emitted

/-- Fresh source occurrence 16: SAME typed values and complete Result continuation. Support until concrete child installation. -/
theorem occurrence_masked_terminal {H W : Type} (c : Calls) (s : Parent H W) (running : Q) (q2 : Q) (q3 : Q) (alpha : Alpha) (transcript1 : r1_wire.SemanticTranscript H) (val1 : Claims) (val3 : K29) (r4 : core.result.Result r1_wire.ValidatedRecord r1_wire.Error) :
 f_masked_terminal c s running q2 q3 alpha transcript1 val1 val3 r4 = (do
    let aspis_coredigestDigest32Inst := s.digest
    let public1 := s.publicValue
    let prefix1 := s.prefixValue
    let transcript := s.transcript
    let challenges := s.challenges
    let obs := s.observer
    let masked_terminal ← c.c4 q2 q3
    f_b c s running masked_terminal alpha transcript1 val1 val3 r4) := rfl
#print axioms occurrence_masked_terminal
end AspisR1.NNG_SourceSuffixes
