import NMX_ActualRoot
import NMX_Match00
import NMX_FoldedProgram
set_option autoImplicit false
noncomputable section
namespace NMX_CutValueBridge
open Aeneas Aeneas.Std Result AdapterRw NMX_OwnedPackets NMX_Program NMX_SourceModel
/-- The55 explicit local congruence proofs meet the exact emitted factor.
Normal-allocation VALUE/control support only; full native RSL interpretation
and independently aborting allocations are separate. -/
theorem normalized (ops : Ops) (owners : Owners) (verifier : solana_pubkey.Pubkey)
 (accounts : Slice r1_pool_adapter.owned.OwnedAccount) (pool : solana_pubkey.Pubkey)
 (outputLane : U8) (slot : U64) :
 NMX_FoldedProgram.normalized ops owners verifier accounts pool outputLane slot =
 NMX_Emitted.auth ops ops.op50 (r1_pool_adapter.owned.authenticate_invariant_release_registry ops)
  verifier accounts pool outputLane slot := by
 rw [NMX_ActualRoot.factor ops owners]
 by_cases count : Slice.len accounts = 7#usize
 · simp only [NMX_FoldedProgram.normalized,count,bne,beq_self_eq_true,
    Bool.not_true,Bool.false_eq_true,↓reduceIte]
   exact NMX_Match00.e001 owners ops verifier accounts pool outputLane slot
 · simp [NMX_FoldedProgram.normalized,count]

theorem source (ops : Ops) (owners : Owners) (verifier : solana_pubkey.Pubkey)
 (accounts : Slice r1_pool_adapter.owned.OwnedAccount) (pool : solana_pubkey.Pubkey)
 (outputLane : U8) (slot : U64) :
 NMX_ValueLink.erase (eval (NMX_SourceModel.source ops owners)
  (NMX_SourceProgram.auth ops verifier accounts pool outputLane slot) ()) =
 NMX_Emitted.auth ops ops.op50 (r1_pool_adapter.owned.authenticate_invariant_release_registry ops)
  verifier accounts pool outputLane slot :=
 (NMX_FoldedProgram.erased ops owners verifier accounts pool outputLane slot).trans
  (normalized ops owners verifier accounts pool outputLane slot)
#print axioms normalized
#print axioms source
end NMX_CutValueBridge
end
