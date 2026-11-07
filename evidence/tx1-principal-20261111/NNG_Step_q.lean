import NNG_SourceSuffixes
set_option autoImplicit false
noncomputable section
namespace AspisR1.NNG_SourceSuffixes
open Aeneas Aeneas.Std Result NNG_verify_finish NNG_Emitted

/-- Fresh source occurrence 9: SAME typed values and complete Result continuation. Support until concrete child installation. -/
theorem occurrence_q {H W : Type} (c : Calls) (s : Parent H W) (running : Q) (val2 : Q) (alpha : Alpha) (transcript1 : r1_wire.SemanticTranscript H) (val1 : Claims) (a : Array Q 16#usize) (a1 : Alpha) (a2 : K29) :
 f_q c s running val2 alpha transcript1 val1 a a1 a2 = (do
    let aspis_coredigestDigest32Inst := s.digest
    let public1 := s.publicValue
    let prefix1 := s.prefixValue
    let transcript := s.transcript
    let challenges := s.challenges
    let obs := s.observer
    let q ← Array.index_usize a2 27#usize
    f_mask c s running val2 q alpha transcript1 val1 a a1) := rfl
#print axioms occurrence_q
end AspisR1.NNG_SourceSuffixes
