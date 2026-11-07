import NMX_R2_CheckpointShape
import NMX_R2_StdOps
set_option autoImplicit false
noncomputable section
namespace NMX_R2_CheckpointCarrier
open Aeneas Aeneas.Std AdapterRw NMX_R2_Carrier
attribute [local instance] Classical.propDecidable

theorem metadata (a : r1_pool_adapter.owned.OwnedAccount) (program : solana_pubkey.Pubkey)
 (writable : Bool) :
 (decide ((account a).owner ≠ key program) || (account a).is_signer || (account a).executable ||
  (account a).is_writable != writable) = NMX_R2_CheckpointShape.bad a program writable := by
 simp only [account,NMX_R2_CheckpointShape.bad,ne_eq,NMX_R2_KeyCarrier.key_equal,decide_not]

theorem size_literal : (1768#usize).val = RSL.CHECKPOINT_BYTES := by
 change (1768#usize).val = 1768
 scalar_tac

theorem size_equal (n : Usize) : n = 1768#usize ↔ n.val = RSL.CHECKPOINT_BYTES := by
 constructor
 · intro h
   simpa only [h,size_literal]
 · intro h
   apply UScalar.eq_of_val_eq
   exact h.trans size_literal.symm

theorem size_ne (n : Usize) : (n != 1768#usize) = (n.val != RSL.CHECKPOINT_BYTES) := by
 change (!(n == 1768#usize)) = (!(n.val == RSL.CHECKPOINT_BYTES))
 apply congrArg Bool.not
 apply Bool.eq_iff_iff.mpr
 simp only [beq_iff_eq,size_equal]

/-- Unused std slots are discarded by the actual emitted helper, not by a
caller hypothesis. Every reached equality/clone/size operation is identical. -/
theorem source (env : RSL.Env) (aborts : Bool) (failure : Error)
 (a : r1_pool_adapter.owned.OwnedAccount) (program : solana_pubkey.Pubkey) (writable : Bool) :
 r1_pool_adapter.owned.require_verifier_checkpoint (NMX_R2_StdOps.install env aborts failure) a program writable =
 r1_pool_adapter.owned.require_verifier_checkpoint
  (NMX_R2_CheckpointShape.install (NMX_R2_PrimitiveInstall.install (NMX_R2_StdOps.unused failure) env)
   aborts failure) a program writable := by
 rfl

#print axioms metadata
#print axioms size_literal
#print axioms size_equal
#print axioms size_ne
#print axioms source
end NMX_R2_CheckpointCarrier
end
