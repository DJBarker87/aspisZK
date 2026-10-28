import NDO_JHc_WriterTotal
set_option autoImplicit false
noncomputable section
namespace AspisR1.JHe_WriterImage
open Aeneas Aeneas.Std Result
open OraclePortCkptAbi2Extracted aspis_r1_cost_probe.verifier
open CheckpointBytes5Effect MultiproofConeCanonical
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisR1Stage2.WireTx2 (singletonParts checksumParts)

/-- Exact image of a successful append-content writer, with all three digest
calls and checksum on the body actually constructed. This does not assert
that the prepared/accumulator values match a retained checkpoint. -/
theorem source {H : Type} (D : AspisR1Stage2.aspis_core.digest.Digest32 H) (hash : H)
    (total : ∀ parts, ∃ out, D.digest hash parts=ok out)
    (p : Prepared) (a : Accumulator) (proof pub : Slice U8) (saved : Slice U8)
    (size : a.weights.val.length=64) (variant : p.variant=.S2) (next : a.next.val=10)
    (run : erase D hash (WAdm_SourceWriter.code p a proof pub)=ok saved) :
    ∃ (hp hu hc : Array U8 32#usize) (body : Slice U8),
      D.digest hash (singletonParts proof)=ok hp ∧
      D.digest hash (singletonParts pub)=ok hu ∧
      WAdm_SourceWriter.toSlice (WAdm_SourceBody.body p a hp hu)=ok body ∧
      D.digest hash (checksumParts body)=ok hc ∧
      body.val.length=1736 ∧
      saved.val=(WAdm_SourceBody.body p a hp hu).map CheckpointBytes5Writer.u8 ++ hc.val := by
  obtain ⟨hp,hpCall⟩ := total (singletonParts proof)
  obtain ⟨hu,huCall⟩ := total (singletonParts pub)
  have len := JHc_WriterTotal.body_length p a hp hu size variant next
  obtain ⟨body,bodyCall,bodyBytes⟩ := JHc_WriterTotal.toSlice_total
    (WAdm_SourceBody.body p a hp hu) (by rw [len];scalar_tac)
  obtain ⟨hc,hcCall⟩ := total (checksumParts body)
  have endLen : (WAdm_SourceBody.body p a hp hu ++ bytesOf hc.val).length=1768 := by
    simp only [List.length_append,len,bytesOf,List.length_map,hc.property]
    rfl
  obtain ⟨out,outCall,outBytes⟩ := JHc_WriterTotal.toSlice_total
    (WAdm_SourceBody.body p a hp hu ++ bytesOf hc.val) (by rw [endLen];scalar_tac)
  have exactRun : erase D hash (WAdm_SourceWriter.code p a proof pub)=ok out := by
    simp only [WAdm_SourceWriter.code,erase_bind,erase_read,erase_lift,hpCall,huCall,
      bodyCall,hcCall,outCall,bind_tc_ok]
  have same : out=saved := Result.ok.inj (exactRun.symm.trans run)
  refine ⟨hp,hu,hc,body,hpCall,huCall,bodyCall,hcCall,?_,?_⟩
  · rw [bodyBytes,List.length_map,len]
  · rw [←same,outBytes,List.map_append,WAdm_SourceWriter.map_bytes]
#print axioms source
end AspisR1.JHe_WriterImage
end
