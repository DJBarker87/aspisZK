import NNG_SourceSuffixes
set_option autoImplicit false
noncomputable section
namespace AspisR1.NNG_SourceSuffixes
open Aeneas Aeneas.Std Result NNG_verify_finish NNG_Emitted

/-- Fresh source occurrence 10: SAME typed values and complete Result continuation. Support until concrete child installation. -/
theorem occurrence_mask {H W : Type} (c : Calls) (s : Parent H W) (running : Q) (val2 : Q) (q : Q) (alpha : Alpha) (transcript1 : r1_wire.SemanticTranscript H) (val1 : Claims) (a : Array Q 16#usize) (a1 : Alpha) :
 f_mask c s running val2 q alpha transcript1 val1 a a1 = (do
    let aspis_coredigestDigest32Inst := s.digest
    let public1 := s.publicValue
    let prefix1 := s.prefixValue
    let transcript := s.transcript
    let challenges := s.challenges
    let obs := s.observer
    let mask ←
      c.c6 a a1 q
        alpha
    f_r4 c s running val2 mask alpha transcript1 val1) := rfl
#print axioms occurrence_mask
end AspisR1.NNG_SourceSuffixes
