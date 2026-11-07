import NNG_SourceSuffixes
set_option autoImplicit false
noncomputable section
namespace AspisR1.NNG_SourceSuffixes
open Aeneas Aeneas.Std Result NNG_verify_finish NNG_Emitted

/-- Fresh source occurrence 3: SAME typed values and complete Result continuation. Support until concrete child installation. -/
theorem occurrence_r2 {H W : Type} (c : Calls) (s : Parent H W) (running : Q) (alpha : Alpha) (transcript1 : r1_wire.SemanticTranscript H) (val1 : Claims) :
 f_r2 c s running alpha transcript1 val1 = (do
    let aspis_coredigestDigest32Inst := s.digest
    let public1 := s.publicValue
    let prefix1 := s.prefixValue
    let transcript := s.transcript
    let challenges := s.challenges
    let obs := s.observer
    let r2 ←
      c.c7
        public1 val1 alpha challenges
    f_r3 c s running alpha transcript1 val1) := rfl
#print axioms occurrence_r2
end AspisR1.NNG_SourceSuffixes
