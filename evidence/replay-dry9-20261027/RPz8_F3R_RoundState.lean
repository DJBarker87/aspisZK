import RPz8_F3R_RoundStep
import RPz7_PSem_RoundCalls
set_option autoImplicit false
noncomputable section
namespace AspisR1.F3R_RoundState
open Aeneas Aeneas.Std Result
open AspisR1PublicPreparation PreparedHashCode SourceDigestLog

theorem state {Hash : Type} {D : aspis_core.Digest32 Hash} {pre : r1_wire.Prefix}
    (B : RoundModel.Boundaries) (c : SourceFull25.Call D pre)
    (alpha : Array aspis_core.field.QM31 10#usize) (running : aspis_core.field.QM31)
    (round : Usize) (row : 15#u8+UScalar.cast .U8 round=ok c.row)
    (out : aspis_core.field.QM31 × Array aspis_core.field.QM31 10#usize × r1_wire.SemanticTranscript Hash)
    (success : erase (S1SemanticCode.roundStep B D pre c.before alpha running round)=ok (.Ok out)) :
    out.2.2=c.after := by
  have raw := (S1SemanticCode.roundStep_erasure B D pre c.before alpha running round).symm.trans success
  obtain ⟨record,q,read,semantic,updated⟩ := AspisR1PublicPreparation.PSem_RoundCalls.step_success
    B D pre c.before out.2.2 alpha out.2.1 running out.1 round c.row row raw
  have same : record=c.record := core.result.Result.Ok.inj (Result.ok.inj (read.symm.trans c.validated))
  subst record
  exact congrArg Prod.snd (Result.ok.inj (semantic.symm.trans c.semantic))

#print axioms state
end AspisR1.F3R_RoundState
end
