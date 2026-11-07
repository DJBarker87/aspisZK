import NNG_SourceSuffixes
set_option autoImplicit false
noncomputable section
namespace AspisR1.NNG_SourceSuffixes
open Aeneas Aeneas.Std Result NNG_verify_finish NNG_Emitted

/-- Fresh source occurrence 5: SAME typed values and complete Result continuation. Support until concrete child installation. -/
theorem occurrence_mark3 {H W : Type} (c : Calls) (s : Parent H W) (running : Q) (val2 : Q) (alpha : Alpha) (transcript1 : r1_wire.SemanticTranscript H) (val1 : Claims) :
 f_mark3 c s running val2 alpha transcript1 val1 = (do
    let aspis_coredigestDigest32Inst := s.digest
    let public1 := s.publicValue
    let prefix1 := s.prefixValue
    let transcript := s.transcript
    let challenges := s.challenges
    let obs := s.observer
    c.c9 obs 3#u8
    f_a c s running val2 alpha transcript1 val1) := rfl
#print axioms occurrence_mark3
end AspisR1.NNG_SourceSuffixes
