import NNT_RelReplay241
import NMX_R9_Head241
import NMX_R9_GroupHead241
import NMX_R8_Digest241
set_option autoImplicit false
noncomputable section
namespace NNT_Native241
open Aeneas Aeneas.Std Result AdapterRw NMS_R2N_Interpreted
abbrev Reply := core.result.Result Unit solana_program_error.ProgramError
abbrev L := LIBB_PoolLib.library
abbrev D := LIBB_PoolLib.deployed
abbrev V := LIBB_V2Star.library

/-- Every native source observation, including all244/064 stops, refines the
exact canonical241 law. D1/D2 are the only original-input clauses. -/
theorem full (choices : NMX_R4_Authentication.Choices)
 (p : solana_pubkey.Pubkey) (accounts : Slice r1_pool_adapter.owned.OwnedAccount)
 (data : Slice U8) (slot : core.result.Result U64 solana_program_error.ProgramError)
 (R0 : RSL.Bytes → RSL.Bytes → Prop)
 (w : RSL.Bytes → RSL.Bytes → RSL.Bytes → RSL.Spec (Except V.VErr Unit))
 (h : RSL.NNT.LawRefines V R0 w)
 (domain : RSL.TX2_241.Domain (RSL.TAS.lib V R0 w) (NMX_R9_ArgsNative241.args p accounts data slot)) :
 Simulates (NMS_R2N_RSLError.reply id) (NMX_R9_Native241.meaning choices p accounts data slot)
  (RSL.TX2_241.Ref L D (RSL.TAS.lib V R0 w) (NMX_R9_ArgsNative241.args p accounts data slot)) := by
 intro env o run
 change NMS_Effect241.stage2 (NMX_R8_Std241.ops env) (NMX_R9_Children241.original choices)
  p accounts data slot env o at run
 rw [NMX_R9_GroupHead241.source,←NMX_R8_Factor241.source] at run
 have observed := NMX_R9_Head241.full env choices p accounts data slot env o run
 exact NNT_RelReplay241.fold R0 w _ domain h env _ observed
#print axioms full
end NNT_Native241
end
