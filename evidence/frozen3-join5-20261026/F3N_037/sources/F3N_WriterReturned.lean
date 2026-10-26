import F3N_CheckpointRun
import Tx2N_Reader
set_option autoImplicit false
noncomputable section
namespace AspisR1.F3N_WriterReturned
open Aeneas Aeneas.Std Result AspisR1Stage2 CheckpointBytes5Effect CheckpointBytes3Namespaces

theorem erased {Hash : Type} (D : VTop_Stages.aspis_core.digest.Digest32 Hash) (hash : Hash)
    (p : verifier.Prepared) (a : verifier.Accumulator) (proof pub : Slice U8)
    (saved : alloc.vec.Vec U8)
    (success : Port3_CheckpointInstall.writer D p a proof pub hash=ok saved) :
    erase (VTop_Checkpoint.digest D) hash
      (CheckpointBytes5Writer.writer (toPrepared p) (toAccumulator a) proof pub)=
        ok (alloc.vec.Vec.deref saved) := by
  unfold Port3_CheckpointInstall.writer at success
  obtain ⟨ck,called,returned⟩ := OraclePortCkptAbiTry.bind_success _ _ _ success
  have same : (⟨ck.val,ck.property⟩ : alloc.vec.Vec U8)=saved := Result.ok.inj returned
  have values := congrArg (fun v : alloc.vec.Vec U8=>v.val) same
  have slices : ck=alloc.vec.Vec.deref saved := Subtype.ext values
  rw [← slices]
  exact called

#print axioms erased
end AspisR1.F3N_WriterReturned
end
