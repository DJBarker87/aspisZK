import NNG_SourceSuffixes
set_option autoImplicit false
noncomputable section
namespace AspisR1.NNG_SourceSuffixes
open Aeneas Aeneas.Std Result NNG_verify_finish NNG_Emitted

/-- Fresh source occurrence 15: SAME typed values and complete Result continuation. Support until concrete child installation. -/
theorem occurrence_q3 {H W : Type} (c : Calls) (s : Parent H W) (running : Q) (q2 : Q) (alpha : Alpha) (transcript1 : r1_wire.SemanticTranscript H) (val1 : Claims) (val3 : K29) (r4 : core.result.Result r1_wire.ValidatedRecord r1_wire.Error) :
 f_q3 c s running q2 alpha transcript1 val1 val3 r4 = (do
    let aspis_coredigestDigest32Inst := s.digest
    let public1 := s.publicValue
    let prefix1 := s.prefixValue
    let transcript := s.transcript
    let challenges := s.challenges
    let obs := s.observer
    let q3 ← Array.index_usize val3 28#usize
    f_masked_terminal c s running q2 q3 alpha transcript1 val1 val3 r4) := rfl
#print axioms occurrence_q3
end AspisR1.NNG_SourceSuffixes
