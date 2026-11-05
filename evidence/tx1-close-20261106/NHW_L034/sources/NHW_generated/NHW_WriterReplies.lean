import NHW_ModelWriter
set_option autoImplicit false
noncomputable section
namespace AspisR1.NHW_WriterReplies
open Aeneas Aeneas.Std Result AspisR1Stage2
open CheckpointBytes5Effect CheckpointBytes5Writer
open AspisR1Stage2.WireTx2 (singletonParts checksumParts)
/-- Extract the three replies from this exact source-program execution. The
checksum query uses the body determined by its first two replies. -/
theorem source {H : Type} (D : aspis_core.digest.Digest32 H) (hash : H)
 (p : Prepared) (a : Accumulator) (domain : NGC_KNE_Caller.WriterDomain p a)
 (proof pub saved : Slice U8)
 (accepted : erase D hash (NGC_KNE_Writer.sourceProgram p a domain proof pub)=ok saved) :
 ∃ hp hu hc : Digest,
 D.digest hash (singletonParts proof)=ok hp ∧
 D.digest hash (singletonParts pub)=ok hu ∧
 D.digest hash (checksumParts (NGC_KNE_Writer.materialize p a domain hp hu))=ok hc ∧
 saved=NGC_KNE_Writer.returned p a domain hp hu hc := by
 rw [NGC_KNE_Writer.program_eq] at accepted
 simp only [NGC_LPm_CheckpointProgram.native,CheckpointBytes5Effect.erase_bind,CheckpointBytes5Effect.read,CheckpointBytes5Effect.erase,bind_tc_ok] at accepted
 obtain ⟨hp,proofCall,accepted⟩ := Port3_PushFrame.bind_success _ _ _ accepted
 obtain ⟨hu,publicCall,accepted⟩ := Port3_PushFrame.bind_success _ _ _ accepted
 obtain ⟨hc,checksumCall,accepted⟩ := Port3_PushFrame.bind_success _ _ _ accepted
 refine ⟨hp,hu,hc,proofCall,publicCall,?_,?_⟩
 · rw [NGC_KNE_Writer.materialize_eq]
   exact checksumCall
 · rw [NGC_KNE_Writer.returned_eq]
   exact (Result.ok.inj accepted).symm
#print axioms source
end AspisR1.NHW_WriterReplies
