import RawJ_SampleRead
import S1SemanticCodeSemanticValidatedV1
set_option autoImplicit false
noncomputable section
namespace AspisR1.RawJ_ValidatedRead
open Aeneas Aeneas.Std Result FS2.Duplex
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep AspisV8R19.SqueezeOracleBridge
open AspisR1PublicPreparation AspisR1PublicPreparation.PreparedHashCode AuS1_Suffix

theorem frame {H : Type} (D : aspis_core.Digest32 H) (self after : r1_wire.SemanticTranscript H)
    (record : r1_wire.ValidatedRecord) (out : aspis_core.field.QM31)
    (success : erase (S1SemanticCode.semanticValidated D self record) = ok (.Ok out,after)) :
    ∃ tag, (160#u8+record.row : Result U8) = ok tag ∧
      Read (observe (run (S1SemanticCode.semanticValidated D self record)).1)
        (flatten (RawJ_SampleRead.parts self.state tag record.framed)) := by
  let log := observe (run (S1SemanticCode.semanticValidated D self record)).1
  have inc : ∀ frame, Read (observe (run (S1SemanticCode.semanticValidated D self record)).1) frame →
      Read log frame := fun _ h => h
  change ∃ tag, _ ∧ Read log _
  unfold S1SemanticCode.semanticValidated at success inc
  obtain ⟨row,hr,s1,sub1⟩ := right_read _ _ _ success
  rw [erase_lift] at hr
  have same : record.row = row := Result.ok.inj hr
  subst row
  split at s1
  · cases s1
  · rename_i branch
    obtain ⟨framed,hf,s2,sub2⟩ := right_read _ _ _ s1
    rw [erase_lift] at hf
    have same : record.framed = framed := Result.ok.inj hf
    subst framed
    obtain ⟨pair,hp,s3,sub3⟩ := right_read _ _ _ s2
    rcases pair with ⟨result,transcript⟩
    obtain ⟨cf,hcf,s4,sub4⟩ := right_read _ _ _ s3
    cases cf with
    | Break residual =>
      simp only [erase_bind,erase_lift,erase_pure] at s4
      repeat' first | (solve | cases s4) | uncase_result | head_reduce s4 | split at s4
    | Continue block =>
      rw [erase_lift] at hcf
      cases result with
      | Err e => cases hcf
      | Ok actual =>
        have same : actual = block := by simpa [core.result.Result.Insts.CoreOpsTry.branch] using hcf
        subst actual
        obtain ⟨tag,htag,read⟩ := RawJ_SampleRead.frame D self transcript record.row record.framed block hp
        refine ⟨tag,htag,?_⟩
        have member := left_read _ _ _ s2 _ read
        have moved := sub2 _ member
        apply inc
        apply sub1
        simpa only [if_neg branch] using moved

#print axioms frame
end AspisR1.RawJ_ValidatedRead
end
