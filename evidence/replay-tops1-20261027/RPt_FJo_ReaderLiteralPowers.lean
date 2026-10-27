import RPt_FJo_GammaPersistence
import RPt_FJl_ReaderPowers
set_option autoImplicit false
noncomputable section
namespace AspisR1.FJo_ReaderLiteralPowers
open Aeneas Aeneas.Std Result AspisR1Stage2
open MultiproofConeCanonical OraclePortCkptAbi4Decode
/-- The resumed array uses the writer's SAME gamma, by actual byte persistence. -/
theorem value {Hash : Type} (base : VTop_Stages.Ops) (reserved : Bool)
    (D : VTop_Stages.aspis_core.digest.Digest32 Hash) (hash : Hash)
    (checkpoint proof0 pub0 proof1 pub1 : Slice U8) (saved : alloc.vec.Vec U8)
    (p0 p1 : verifier.Prepared) (a0 a1 : verifier.Accumulator)
    (g : Array FIp_DotsAdapter.E 29#usize) (gamma : AspisWideTower.WideExact)
    (canonical : CanonicalWide (CheckpointBytes3Namespaces.toE p0.gamma))
    (write : Port3_CheckpointInstall.writer D p0 a0 proof0 pub0 hash=ok saved)
    (same : bytesOf checkpoint.val=bytesOf saved.val)
    (read : Port4A_ReaderInstall.reader reserved D checkpoint proof1 pub1 .S2 hash=ok (.Ok (p1,a1)))
    (powers : Tx2N_Powers.powers 29#usize p1.gamma=ok g)
    (literal : CheckpointBytes5Output.ofE p0.gamma=gamma) :
    FIo_ArrayCanon.Holds (FIp_DotsAdapter.toArray g) ∧
      ∀ l : Fin 29,FIp_ArrayValue.value (FIp_DotsAdapter.toArray g) l.val=gamma^l.val := by
  have source := Port4A_ReaderInstall.accepted_source base reserved D hash checkpoint proof1 pub1 .S2 p1 a1 read
  have fields := FJo_GammaPersistence.value reserved D p0 p1 a0 a1 checkpoint proof0 pub0 proof1 pub1 hash saved canonical write same source
  have values := FJl_ReaderPowers.value base reserved D hash checkpoint proof1 pub1 p1 a1 g read powers
  exact ⟨values.1,fun l=>by rw [values.2 l,fields,literal]⟩
#print axioms value
end AspisR1.FJo_ReaderLiteralPowers
end
