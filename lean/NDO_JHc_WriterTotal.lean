import RPz7_WAdm_FissionedFields
import RPz7_WAdm_SourceWriter
set_option autoImplicit false
noncomputable section
namespace AspisR1.JHc_WriterTotal
open Aeneas Aeneas.Std Result
open OraclePortCkptAbi2Extracted aspis_r1_cost_probe.verifier
open CheckpointBytes5Effect CheckpointBytes3Namespaces MultiproofConeCanonical
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisR1Stage2.WireTx2 (singletonParts checksumParts)

theorem body_length (p : Prepared) (a : Accumulator) (hp hu : Array U8 32#usize)
    (size : a.weights.val.length=64) (variant : p.variant=.S2) (next : a.next.val=10) :
    (WAdm_SourceBody.body p a hp hu).length=1736 := by
  have h := congrArg List.length (WAdm_FissionedFields.body_bytes p a hp hu variant next)
  simp only [bytesOf,List.length_map] at h
  rw [WAdm_FissionedContent.body_length _ _ _ _ size] at h
  exact h.symm
#print axioms body_length

theorem toSlice_total (bs : Bytes) (size : bs.length≤Usize.max) :
    ∃ out, WAdm_SourceWriter.toSlice bs=ok out ∧ out.val=bs.map CheckpointBytes5Writer.u8 := by
  let out : Slice U8 := ⟨bs.map CheckpointBytes5Writer.u8,by simpa only [List.length_map] using size⟩
  refine ⟨out,?_,rfl⟩
  simp only [WAdm_SourceWriter.toSlice,dif_pos size]
  rfl
#print axioms toSlice_total

/-- The source append-content writer returns its actual bytes under only
size/control guards and total digest calls. No output bytes are supplied. -/
theorem code_total {H : Type} (D : AspisR1Stage2.aspis_core.digest.Digest32 H) (hash : H)
    (total : ∀ parts, ∃ out, D.digest hash parts=ok out)
    (p : Prepared) (a : Accumulator) (proof pub : Slice U8)
    (size : a.weights.val.length=64) (variant : p.variant=.S2) (next : a.next.val=10) :
    ∃ saved, erase D hash (WAdm_SourceWriter.code p a proof pub)=ok saved ∧ saved.val.length=1768 := by
  obtain ⟨hp,hpCall⟩ := total (singletonParts proof)
  obtain ⟨hu,huCall⟩ := total (singletonParts pub)
  have len := body_length p a hp hu size variant next
  obtain ⟨buf,bufCall,bufBytes⟩ := toSlice_total (WAdm_SourceBody.body p a hp hu)
    (by rw [len];scalar_tac)
  obtain ⟨hc,hcCall⟩ := total (checksumParts buf)
  have finalLen : (WAdm_SourceBody.body p a hp hu ++ bytesOf hc.val).length=1768 := by
    simp only [List.length_append,len,bytesOf,List.length_map,hc.property]
    rfl
  obtain ⟨saved,saveCall,saveBytes⟩ := toSlice_total
    (WAdm_SourceBody.body p a hp hu ++ bytesOf hc.val) (by rw [finalLen];scalar_tac)
  refine ⟨saved,?_,?_⟩
  · simp only [WAdm_SourceWriter.code,erase_bind,erase_read,erase_lift,hpCall,huCall,
      bufCall,hcCall,saveCall,bind_tc_ok]
  · rw [saveBytes,List.length_map,finalLen]
#print axioms code_total
end AspisR1.JHc_WriterTotal
end
