import NNG_SourceSuffixes
set_option autoImplicit false
noncomputable section
namespace AspisR1.NNG_SourceSuffixes
open Aeneas Aeneas.Std Result NNG_verify_finish NNG_Emitted

/-- Fresh source occurrence 7: SAME typed values and complete Result continuation. Support until concrete child installation. -/
theorem occurrence_a1 {H W : Type} (c : Calls) (s : Parent H W) (running : Q) (val2 : Q) (alpha : Alpha) (transcript1 : r1_wire.SemanticTranscript H) (val1 : Claims) (a : Array Q 16#usize) :
 f_a1 c s running val2 alpha transcript1 val1 a = (do
    let aspis_coredigestDigest32Inst := s.digest
    let public1 := s.publicValue
    let prefix1 := s.prefixValue
    let transcript := s.transcript
    let challenges := s.challenges
    let obs := s.observer
    let a1 ←
      c.c0 10#usize
        (r1_semantic.verify_finish.closure_2.Insts.CoreOpsFunctionFnMutTupleUsizeQM31
        aspis_coredigestDigest32Inst) val1
    f_a2 c s running val2 alpha transcript1 val1 a a1) := rfl
#print axioms occurrence_a1
end AspisR1.NNG_SourceSuffixes
