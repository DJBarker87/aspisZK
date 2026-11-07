import NMX_R2_NativeExecution
import NMX_R2_SyntaxFactor
import NMX_R2_LengthGuard
set_option autoImplicit false
noncomputable section
namespace NMX_R2_CountNative
open Aeneas Aeneas.Std AdapterRw NMX_SourceModel NMX_R2_Carrier
/-- Malformed counts reject before every native command; the event prefix is
empty on both variants, independent of child observations and allocator bits. -/
theorem source (owners : Owners) (alloc : NMX_R2_NativeExecution.Allocations) (failure : Error)
 (ln : NMX_R2_RawChildren.LaneNative) (rn : NMX_R2_RawChildren.RegistryNative)
 (verifier : solana_pubkey.Pubkey) (accounts : Slice r1_pool_adapter.owned.OwnedAccount)
 (pool : solana_pubkey.Pubkey) (outputLane : U8) (slot : U64) (env : RSL.Env)
 (count : accounts.val.length ≠ 7) :
 NMX_R2_NativeExecution.run owners alloc failure ln rn env
  (NMX_R2_Skeleton.auth verifier accounts pool outputLane slot) =
 ⟨.ret (.error (if accounts.val.length < 7 then .notEnoughAccountKeys else .invalidArgument)),[]⟩ := by
 have scalarCount : Slice.len accounts ≠ 7#usize :=
  fun equal => count ((NMX_R2_LengthGuard.equal accounts).mp equal)
 rw [NMX_R2_SyntaxFactor.factor]
 by_cases short : accounts.val.length < 7
 · have scalarShort := (NMX_R2_LengthGuard.less accounts).mpr short
   simp [bne,scalarCount,scalarShort,short,NMX_R2_NativeExecution.run,error]
 · have scalarLong : ¬ Slice.len accounts < 7#usize :=
    fun h => short ((NMX_R2_LengthGuard.less accounts).mp h)
   simp [bne,scalarCount,scalarLong,short,NMX_R2_NativeExecution.run,error]
#print axioms source
end NMX_R2_CountNative
end
