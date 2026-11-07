import NNG_SourceSuffixes
set_option autoImplicit false
noncomputable section
namespace AspisR1.NNG_SourceSuffixes
open Aeneas Aeneas.Std Result NNG_verify_finish NNG_Emitted

/-- Fresh source occurrence 17: SAME typed values and complete Result continuation. Support until concrete child installation. -/
theorem occurrence_b {H W : Type} (c : Calls) (s : Parent H W) (running : Q) (masked_terminal : Q) (alpha : Alpha) (transcript1 : r1_wire.SemanticTranscript H) (val1 : Claims) (val3 : K29) (r4 : core.result.Result r1_wire.ValidatedRecord r1_wire.Error) :
 f_b c s running masked_terminal alpha transcript1 val1 val3 r4 = (do
    let aspis_coredigestDigest32Inst := s.digest
    let public1 := s.publicValue
    let prefix1 := s.prefixValue
    let transcript := s.transcript
    let challenges := s.challenges
    let obs := s.observer
    let b ←
      core.cmp.PartialEq.ne.trait_default
        (aspis_core.field.QM31.Insts.CoreCmpPartialEqQM31 c.c3) running
        masked_terminal
    f_terminalGuard c s alpha transcript1 val1 val3 b r4) := rfl
#print axioms occurrence_b
end AspisR1.NNG_SourceSuffixes
