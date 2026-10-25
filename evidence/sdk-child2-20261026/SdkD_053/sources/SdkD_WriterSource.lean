import SdkD_WriterCells
set_option autoImplicit false
noncomputable section
namespace AspisR1.SdkD_WriterSource
open Aeneas Aeneas.Std Result
open CheckpointBytes5Effect

/-- Actual writer result, with its literal three native digest replies. No
canonical field model or ten-step state equation is required. -/
theorem returned {Hash : Type} (D : VTop_Stages.aspis_core.digest.Digest32 Hash)
    (p : AspisR1Stage2.verifier.Prepared) (a : AspisR1Stage2.verifier.Accumulator)
    (proof pub : Slice U8) (hash : Hash) (saved : alloc.vec.Vec U8)
    (success : Port3_CheckpointInstall.writer D p a proof pub hash = ok saved) :
    ∃ hp hu hc : Array U8 32#usize,
      saved.val = (CheckpointBytes5Writer.finish (CheckpointBytes3Namespaces.toPrepared p)
        (CheckpointBytes3Namespaces.toAccumulator a) hp hu hc).val := by
  unfold Port3_CheckpointInstall.writer at success
  obtain ⟨ck,hck,rest⟩ := OraclePortCkptAbiTry.bind_success _ _ _ success
  have bytes := congrArg (fun v : alloc.vec.Vec U8 => v.val) (Result.ok.inj rest)
  simp only [CheckpointBytes5Writer.writer,erase_bind,erase_read,erase_pure] at hck
  obtain ⟨hp,hpCall,tail⟩ := OraclePortCkptAbiTry.bind_success _ _ _ hck
  obtain ⟨hu,huCall,tail⟩ := OraclePortCkptAbiTry.bind_success _ _ _ tail
  obtain ⟨hc,hcCall,tail⟩ := OraclePortCkptAbiTry.bind_success _ _ _ tail
  have same := Result.ok.inj tail
  subst ck
  exact ⟨hp,hu,hc,bytes.symm⟩

#print axioms returned
end AspisR1.SdkD_WriterSource
end
