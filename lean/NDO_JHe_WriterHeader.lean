import NDO_JHe_WriterImage
import NDO_JFq_AuthBytes
set_option autoImplicit false
noncomputable section
namespace AspisR1.JHe_WriterHeader
open Aeneas Aeneas.Std Result
open OraclePortCkptAbi2Extracted aspis_r1_cost_probe.verifier
open CheckpointBytes5Effect MultiproofConeCanonical

/-- Source-selected saved bytes have the same sixteen-byte header as the
retained checkpoint. This is only a prefix equality, not full byte identity. -/
theorem source {H : Type} (D : AspisR1Stage2.aspis_core.digest.Digest32 H) (hash : H)
    (total : ∀ parts, ∃ out, D.digest hash parts=ok out)
    (p : Prepared) (a : Accumulator) (proof pub : Slice U8) (saved : Slice U8)
    (size : a.weights.val.length=64) (variant : p.variant=.S2) (next : a.next.val=10)
    (run : erase D hash (WAdm_SourceWriter.code p a proof pub)=ok saved) :
    saved.val.take 16=JFx_NativeBytes.checkpoint.val.take 16 := by
  obtain ⟨hp,hu,hc,body,_hp,_hu,_body,_hc,_size,image⟩ :=
    JHe_WriterImage.source D hash total p a proof pub saved size variant next run
  have bodyEq := congrArg (List.map CheckpointBytes5Writer.u8)
    (WAdm_FissionedFields.body_bytes p a hp hu variant next)
  rw [WAdm_SourceWriter.map_bytes] at bodyEq
  rw [image,←bodyEq]
  unfold WAdm_FissionedContent.body
  simp only [List.append_assoc]
  change (WAdm_FissionedContent.header ++ _).take 16=_
  rw [←show WAdm_FissionedContent.header.length=16 from rfl,List.take_left]
  exact JFq_AuthBytes.first16.symm
#print axioms source
end AspisR1.JHe_WriterHeader
end
