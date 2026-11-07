import NMX_Actual00
import NMX_EmittedLinks
set_option autoImplicit false
noncomputable section
namespace NMX_ActualRoot
open Aeneas Aeneas.Std Result AdapterRw NMX_OwnedPackets NMX_SourceModel
/-- Literal emitted syntax factored into its55 continuation nodes. No
monadic congruence, child unfolding, or global outcome splitting occurs here. -/
theorem factor (ops : Ops) (owners : Owners) (verifier : solana_pubkey.Pubkey)
 (accounts : Slice r1_pool_adapter.owned.OwnedAccount) (pool : solana_pubkey.Pubkey)
 (outputLane : U8) (slot : U64) :
 NMX_Emitted.auth ops ops.op50 (r1_pool_adapter.owned.authenticate_invariant_release_registry ops)
  verifier accounts pool outputLane slot =
 (if Slice.len accounts = 7#usize then
  NMX_Actual00.t001 owners ops verifier accounts pool outputLane slot
 else if Slice.len accounts < 7#usize then ok (.Err .NotEnoughAccountKeys)
 else ok (.Err .InvalidArgument)) := by
 unfold NMX_Emitted.auth NMX_Actual00.t001 NMX_Actual00.t002 NMX_Actual00.t003 NMX_Actual00.t004 NMX_Actual00.t005 NMX_Actual00.t006 NMX_Actual00.t007 NMX_Actual00.t008 NMX_Actual00.t009 NMX_Actual00.t010 NMX_Actual01.t011 NMX_Actual01.t012 NMX_Actual01.t013 NMX_Actual01.t014 NMX_Actual01.t015 NMX_Actual01.t016 NMX_Actual01.t017 NMX_Actual01.t018 NMX_Actual01.t019 NMX_Actual01.t020 NMX_Actual02.t021 NMX_Actual02.t022 NMX_Actual02.t023 NMX_Actual02.t024 NMX_Actual02.t025 NMX_Actual02.t026 NMX_Actual02.t027 NMX_Actual02.t028 NMX_Actual02.t029 NMX_Actual02.t030 NMX_Actual03.t031 NMX_Actual03.t032 NMX_Actual03.t033 NMX_Actual03.t034 NMX_Actual03.t035 NMX_Actual03.t036 NMX_Actual03.t037 NMX_Actual03.t038 NMX_Actual03.t039 NMX_Actual03.t040 NMX_Actual04.t041 NMX_Actual04.t042 NMX_Actual04.t043 NMX_Actual04.t044 NMX_Actual04.t045 NMX_Actual04.t046 NMX_Actual04.t047 NMX_Actual04.t048 NMX_Actual04.t049 NMX_Actual04.t050 NMX_Actual05.t051 NMX_Actual05.t052 NMX_Actual05.t053 NMX_Actual05.t054 NMX_Actual05.t055
 rfl
#print axioms factor
end NMX_ActualRoot
end
