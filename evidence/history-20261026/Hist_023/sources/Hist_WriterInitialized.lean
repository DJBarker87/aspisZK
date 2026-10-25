import Hist_SourceMarker
import Port3_CheckpointInstall
set_option autoImplicit false
noncomputable section
namespace AspisR1.Hist_WriterInitialized
open Aeneas Aeneas.Std Result
open CheckpointBytes5Effect CheckpointBytes5Writer Hist_Store

theorem accepted_marker {H : Type} (D : AspisR1Stage2.aspis_core.digest.Digest32 H)
    (hash : H) (p : Prepared) (a : Accumulator) (proof pub ck : Slice U8)
    (accepted : erase D hash (writer p a proof pub) = ok ck) : Initialized ck := by
  simp only [writer,erase_bind,erase_read,erase_pure] at accepted
  obtain ⟨hp,_,tail⟩ := OraclePortCkptAbiTry.bind_success _ _ _ accepted
  obtain ⟨hu,_,tail⟩ := OraclePortCkptAbiTry.bind_success _ _ _ tail
  obtain ⟨hc,_,tail⟩ := OraclePortCkptAbiTry.bind_success _ _ _ tail
  have same := Result.ok.inj tail
  subst ck
  exact Hist_SourceMarker.finish_initialized p a hp hu hc

/-- This installed writer call is exported on WAdm's original accepted pair.
No separate checkpoint-marker or nonzero-byte premise is required there. -/
theorem installed_marker {H : Type} (D : VTop_Stages.aspis_core.digest.Digest32 H)
    (hash : H) (p : VTop_Stages.verifier.Prepared) (a : VTop_Stages.verifier.Accumulator)
    (proof pub : Slice U8) (saved : alloc.vec.Vec U8)
    (accepted : Port3_CheckpointInstall.writer D p a proof pub hash = ok saved) :
    Initialized saved.deref := by
  unfold Port3_CheckpointInstall.writer at accepted
  obtain ⟨ck,call,returned⟩ := OraclePortCkptAbiTry.bind_success _ _ _ accepted
  have same := Result.ok.inj returned
  subst saved
  have marker := accepted_marker (VTop_Checkpoint.digest D) hash
    (CheckpointBytes3Namespaces.toPrepared p) (CheckpointBytes3Namespaces.toAccumulator a)
    proof pub ck call
  have eq : (⟨ck.val,ck.property⟩ : alloc.vec.Vec U8).deref = ck := Subtype.ext rfl
  rw [eq]
  exact marker

#print axioms accepted_marker
#print axioms installed_marker
end AspisR1.Hist_WriterInitialized
end
