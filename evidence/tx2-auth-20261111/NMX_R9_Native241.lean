import NMX_R9_Head241
import NMX_R9_GroupHead241
import NMX_R8_Digest241
set_option autoImplicit false
noncomputable section
namespace NMX_R9_Native241
open Aeneas Aeneas.Std Result AdapterRw NMS_R2N_Interpreted
abbrev Reply := core.result.Result Unit solana_program_error.ProgramError
abbrev L := LIBB_PoolLib.library
abbrev D := LIBB_PoolLib.deployed
abbrev V := LIBB_V2Star.library

/-- Literal emitted NMS body, all native242 observations, full064 library
observations and restored std allocation sites. No abstract Ops remain. -/
def meaning (choices : NMX_R4_Authentication.Choices)
 (p : solana_pubkey.Pubkey) (accounts : Slice r1_pool_adapter.owned.OwnedAccount)
 (data : Slice U8) (slot : core.result.Result U64 solana_program_error.ProgramError) : RSL.Spec Reply :=
 fun env o => NMS_Effect241.stage2 (NMX_R8_Std241.ops env) (NMX_R9_Children241.original choices)
  p accounts data slot env o

/-- Every native source observation, including all244/064 stops, refines the
exact canonical241 law. D1/D2 are the only original-input clauses. -/
theorem full (choices : NMX_R4_Authentication.Choices)
 (p : solana_pubkey.Pubkey) (accounts : Slice r1_pool_adapter.owned.OwnedAccount)
 (data : Slice U8) (slot : core.result.Result U64 solana_program_error.ProgramError)
 (domain : RSL.TX2_241.Domain V (NMX_R9_ArgsNative241.args p accounts data slot)) :
 Simulates (NMS_R2N_RSLError.reply id) (meaning choices p accounts data slot)
  (RSL.TX2_241.Ref L D V (NMX_R9_ArgsNative241.args p accounts data slot)) := by
 intro env o run
 change NMS_Effect241.stage2 (NMX_R8_Std241.ops env) (NMX_R9_Children241.original choices)
  p accounts data slot env o at run
 rw [NMX_R9_GroupHead241.source,←NMX_R8_Factor241.source] at run
 have observed := NMX_R9_Head241.full env choices p accounts data slot env o run
 exact NMX_R9_RelReplay241.fold _ domain env _ observed
#print axioms full
end NMX_R9_Native241
end
