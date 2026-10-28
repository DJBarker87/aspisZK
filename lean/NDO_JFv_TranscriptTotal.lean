import NDO_JFv_RoundArithmetic
import RPz7_SAP_SampleCanonical
set_option autoImplicit false
namespace AspisR1.JFv_TranscriptTotal
open Aeneas Aeneas.Std Result WP
open AspisR1PublicPreparation

def Total {H : Type} (D : aspis_core.Digest32 H) : Prop :=
  ∀ hash parts,∃ block,D.digest hash parts=ok block

@[local step] theorem digest {H : Type} (D : aspis_core.Digest32 H) (total : Total D)
    (hash : H) (parts : Slice (Slice U8)) :
    D.digest hash parts ⦃ _ => True ⦄ := by
  obtain ⟨block,call⟩ := total hash parts
  rw [call,WP.spec_ok];trivial

theorem block {H : Type} (D : aspis_core.Digest32 H) (total : Total D)
    (t : r1_wire.SemanticTranscript H) (row : U8) (frame : Slice U8)
    (same : row=t.next_row) (bound : row.val<27) :
    ∃ block after,r1_wire.SemanticTranscript.sample_block_validated D t row frame=ok (.Ok block,after) ∧
      after.next_row.val=row.val+1 := by
  have spec : r1_wire.SemanticTranscript.sample_block_validated D t row frame
      ⦃ result => ∃ block after,result=(.Ok block,after) ∧ after.next_row.val=row.val+1 ⦄ := by
    unfold r1_wire.SemanticTranscript.sample_block_validated
    step* <;> scalar_tac
  obtain ⟨result,call,block,after,eq,next⟩ := WP.spec_imp_exists spec
  exact ⟨block,after,by rw [eq] at call;exact call,next⟩

#print axioms digest
#print axioms block
end AspisR1.JFv_TranscriptTotal
