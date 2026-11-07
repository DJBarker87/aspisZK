import NNG_SourceSuffixes
set_option autoImplicit false
noncomputable section
namespace AspisR1.NNG_SourceSuffixes
open Aeneas Aeneas.Std Result NNG_verify_finish NNG_Emitted

/-- Fresh source occurrence 8: SAME typed values and complete Result continuation. Support until concrete child installation. -/
theorem occurrence_a2 {H W : Type} (c : Calls) (s : Parent H W) (running : Q) (val2 : Q) (alpha : Alpha) (transcript1 : r1_wire.SemanticTranscript H) (val1 : Claims) (a : Array Q 16#usize) (a1 : Alpha) :
 f_a2 c s running val2 alpha transcript1 val1 a a1 = (do
    let aspis_coredigestDigest32Inst := s.digest
    let public1 := s.publicValue
    let prefix1 := s.prefixValue
    let transcript := s.transcript
    let challenges := s.challenges
    let obs := s.observer
    let a2 ← Array.index_usize val1 0#usize
    f_q c s running val2 alpha transcript1 val1 a a1 a2) := rfl
#print axioms occurrence_a2
end AspisR1.NNG_SourceSuffixes
