import NMX_R8_Head241
import NMX_R8_GroupHead241
import NMX_R8_Digest241
set_option autoImplicit false
noncomputable section
namespace NMX_R8_Native241
open Aeneas Aeneas.Std Result AdapterRw NMS_R2N_Interpreted
abbrev Reply := core.result.Result Unit solana_program_error.ProgramError
abbrev L := LIBB_PoolLib.library
abbrev D := LIBB_PoolLib.deployed
abbrev V := LIBB_V2Star.library

def meaning (choices : NMX_R4_Authentication.Choices)
 (p : solana_pubkey.Pubkey) (accounts : Slice r1_pool_adapter.owned.OwnedAccount)
 (data : Slice U8) (slot : core.result.Result U64 solana_program_error.ProgramError) : RSL.Spec Reply :=
 fun env o => NMS_Effect241.stage2 (NMX_R8_Std241.ops env) (NMX_R8_Children241.original choices)
  p accounts data slot env o

/-- Complete source observation refinement. The only input clauses are the
original canonical D1/D2; all244 widths and entered064 clauses are internal. -/
theorem full (choices : NMX_R4_Authentication.Choices)
 (p : solana_pubkey.Pubkey) (accounts : Slice r1_pool_adapter.owned.OwnedAccount)
 (data : Slice U8) (slot : core.result.Result U64 solana_program_error.ProgramError)
 (domain : RSL.TX2_241.Domain V (NMX_R8_Head241.args p accounts data slot)) :
 Simulates (NMS_R2N_RSLError.reply id) (meaning choices p accounts data slot)
  (RSL.TX2_241.Ref L D V (NMX_R8_Head241.args p accounts data slot)) := by
 intro env o run
 change NMS_Effect241.stage2 (NMX_R8_Std241.ops env) (NMX_R8_Children241.original choices)
  p accounts data slot env o at run
 rw [NMX_R8_GroupHead241.source,←NMX_R8_Factor241.source] at run
 have observed := NMX_R8_Head241.full env choices p accounts data slot env o run
 exact NMX_R8_RelReplay241.fold choices _ domain env _ observed
#print axioms full
end NMX_R8_Native241
end
