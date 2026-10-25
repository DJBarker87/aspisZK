import Hist_WriterInitialized
set_option autoImplicit false
noncomputable section
namespace AspisR1.Hist_WriterShape
open Aeneas Aeneas.Std Result Hist_Store
open CheckpointBytes5Effect CheckpointBytes5Writer

theorem finish_length (p : Prepared) (a : Accumulator) (hp hu hc : Digest) :
    (finish p a hp hu hc).val.length = 1768 := by
  simp only [finish,List.length_append,List.length_map,
    CheckpointBytesDecodeC5.sourceBody,List.length_ofFn,hc.property]
  rfl

theorem accepted_length {H : Type} (D : AspisR1Stage2.aspis_core.digest.Digest32 H)
    (hash : H) (p : Prepared) (a : Accumulator) (proof pub ck : Slice U8)
    (accepted : erase D hash (writer p a proof pub) = ok ck) : ck.val.length = 1768 := by
  simp only [writer,erase_bind,erase_read,erase_pure] at accepted
  obtain ⟨hp,_,tail⟩ := OraclePortCkptAbiTry.bind_success _ _ _ accepted
  obtain ⟨hu,_,tail⟩ := OraclePortCkptAbiTry.bind_success _ _ _ tail
  obtain ⟨hc,_,tail⟩ := OraclePortCkptAbiTry.bind_success _ _ _ tail
  have same := Result.ok.inj tail
  subst ck
  exact finish_length p a hp hu hc

theorem installed_shape {H : Type} (D : VTop_Stages.aspis_core.digest.Digest32 H)
    (hash : H) (p : VTop_Stages.verifier.Prepared) (a : VTop_Stages.verifier.Accumulator)
    (proof pub : Slice U8) (saved : alloc.vec.Vec U8)
    (accepted : Port3_CheckpointInstall.writer D p a proof pub hash = ok saved) :
    Initialized saved.deref ∧ saved.val.length = 1768 := by
  refine ⟨Hist_WriterInitialized.installed_marker D hash p a proof pub saved accepted,?_⟩
  unfold Port3_CheckpointInstall.writer at accepted
  obtain ⟨ck,call,returned⟩ := OraclePortCkptAbiTry.bind_success _ _ _ accepted
  have same := Result.ok.inj returned
  subst saved
  exact accepted_length (VTop_Checkpoint.digest D) hash (CheckpointBytes3Namespaces.toPrepared p)
    (CheckpointBytes3Namespaces.toAccumulator a) proof pub ck call

#print axioms finish_length
#print axioms accepted_length
#print axioms installed_shape
end AspisR1.Hist_WriterShape
end
