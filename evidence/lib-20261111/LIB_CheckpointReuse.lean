import NMX_R2_CheckpointAfter
import NMX_R2_HeterogeneousPrimitives
set_option autoImplicit false
noncomputable section
namespace LIB_CheckpointReuse
open Aeneas Aeneas.Std AdapterRw NMX_R2_Carrier

theorem length (base : Ops) (aborts : Bool) (failure : Error)
 (a : r1_pool_adapter.owned.OwnedAccount) :
 NMX_R2_Heterogeneous.Refines (fun n : Usize => n.val)
  (NMX_R2_ResultRelation.rust
   (r1_pool_adapter.owned.OwnedAccount.data_len (NMX_R2_CheckpointShape.install base aborts failure) a))
  (RSL.OwnedAccount.data_len (account a)) := by
 intro env o run
 change o = NMX_R2_ObserveResult.observe id _ at run
 subst o
 rw [NMX_R2_ResultRelation.map_rust]
 change RSL.OwnedAccount.data_len (account a) env
  (NMX_R2_ObserveResult.observe (fun n : Usize => n.val)
   (r1_pool_adapter.owned.OwnedAccount.data_len (NMX_R2_CloneNative.install base aborts failure) a))
 exact NMX_R2_LengthNative.length base aborts failure a env

theorem tail (n : Usize) :
 NMX_R2_Heterogeneous.Refines id
  (RSL.RS.ofExcept (reply id (NMX_R2_CheckpointTail.tail n)))
  (RSL.RS.check (n.val != RSL.CHECKPOINT_BYTES) .invalidAccountData) := by
 rw [← NMX_R2_CheckpointCarrier.size_ne]
 cases flag : (n != 1768#usize) <;>
  simp only [NMX_R2_CheckpointTail.tail,RSL.RS.check,flag,Bool.false_eq_true,↓reduceIte] <;>
  exact NMX_R2_HeterogeneousPrimitives.refl _

/-- Complete emitted verifier-checkpoint guard, including its nonempty-error
clone abort after the successful metadata prefix. No own-input restriction. -/
theorem packet (env : RSL.Env) (aborts : Bool) (failure : Error)
 (a : r1_pool_adapter.owned.OwnedAccount) (program : solana_pubkey.Pubkey) (writable : Bool) :
 RSL.verifierCheckpoint (account a) (key program) writable env
  (NMX_R2_ObserveResult.observe id
   (r1_pool_adapter.owned.require_verifier_checkpoint (NMX_R2_StdOps.install env aborts failure)
    a program writable)) := by
 rw [NMX_R2_CheckpointCarrier.source,NMX_R2_CheckpointShape.source]
 unfold RSL.verifierCheckpoint
 rw [NMX_R2_CheckpointCarrier.metadata]
 cases flag : NMX_R2_CheckpointShape.bad a program writable with
 | true => simp only [flag,↓reduceIte]; rfl
 | false =>
   simp only [flag,Bool.false_eq_true,↓reduceIte]
   let base := NMX_R2_PrimitiveInstall.install (NMX_R2_StdOps.unused failure) env
   let r := r1_pool_adapter.owned.OwnedAccount.data_len
    (NMX_R2_CheckpointShape.install base aborts failure) a
   have composed : NMX_R2_Heterogeneous.Refines id
    (RSL.RS.bind (NMX_R2_ResultRelation.rust r)
     (fun n => RSL.RS.ofExcept (reply id (NMX_R2_CheckpointTail.tail n))))
    (RSL.RS.bind (RSL.OwnedAccount.data_len (account a))
     (fun n => RSL.RS.check (n != RSL.CHECKPOINT_BYTES) .invalidAccountData)) :=
    NMX_R2_Heterogeneous.bind (fun n : Usize => n.val) id _ _ _ _
     (length base aborts failure a) tail
   have law := composed env _ (NMX_R2_CheckpointAfter.member r env)
   simpa only [NMX_R2_HeterogeneousPrimitives.map_identity] using law
#print axioms length
#print axioms tail
#print axioms packet
end LIB_CheckpointReuse
end
