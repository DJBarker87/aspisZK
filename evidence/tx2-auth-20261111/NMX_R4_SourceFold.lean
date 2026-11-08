import NMX_R4_CallRoot
import NMX_R4_Observed00
import NMX_FoldedProgram
import NMX_R2_StdSource
set_option autoImplicit false
noncomputable section
namespace NMX_R4_SourceFold
open Aeneas Aeneas.Std Result AdapterRw NMX_OwnedPackets NMX_R4_CallRun NMX_R4_CallContext

theorem source (c : Context) (verifier : solana_pubkey.Pubkey)
 (accounts : Slice r1_pool_adapter.owned.OwnedAccount) (pool : solana_pubkey.Pubkey)
 (outputLane : U8) (slot : U64) :
 observe c (NMX_R4_CallRoot.auth c.owners (ops c) verifier accounts pool outputLane slot) =
 NMX_R2_NativeExecution.run c.owners c.allocations c.failure c.lane c.registry c.env
   (NMX_R2_Skeleton.auth verifier accounts pool outputLane slot) := by
 rw [← NMX_R2_StdSource.source c.env c.allocations.clone c.failure]
 change observe c (NMX_R4_CallRoot.auth c.owners (ops c) verifier accounts pool outputLane slot) =
 NMX_R2_NativeExecution.run c.owners c.allocations c.failure c.lane c.registry c.env
   (NMX_SourceProgram.auth (ops c) verifier accounts pool outputLane slot)
 rw [NMX_FoldedProgram.source (ops c) c.owners]
 unfold NMX_R4_CallRoot.auth
 by_cases count : Slice.len accounts = 7#usize
 · simp only [count,beq_self_eq_true,bne,Bool.not_true,Bool.false_eq_true,↓reduceIte]
   exact NMX_R4_Observed00.e001 c verifier accounts pool outputLane slot
 · simp only [count,↓reduceIte]
   have bad : (Slice.len accounts != 7#usize) = true := by simp [count]
   rw [if_pos bad]
   by_cases short : Slice.len accounts < 7#usize <;> simp only [short,↓reduceIte] <;> rfl

#print axioms source
end NMX_R4_SourceFold
end
