import NMX_EmittedLinks
set_option autoImplicit false
noncomputable section
namespace NMX_DirectValueFold
open Aeneas Aeneas.Std Result AdapterRw
abbrev Account := r1_pool_adapter.owned.OwnedAccount
abbrev Master := aspis_statement.pool_v1.pair_forest_accounts.PoolV1PairForestMasterV1
abbrev Lane := aspis_statement.pool_v1.pair_forest_accounts.PoolV1PairForestLaneStateV1
abbrev PE := solana_program_error.ProgramError
abbrev LaneCall := Slice U8 → Result (core.result.Result Lane PE)
abbrev RegistryCall := solana_pubkey.Pubkey → solana_pubkey.Pubkey → Account → Master →
 Account → Account → U64 → Result (core.result.Result Unit PE)
/-- Exact fresh-emitted value/control fold, including every Err/fail/div arm.
These value equalities must be DERIVED from the full child packets and frames;
this support theorem is not a replacement for those packets or a row root. -/
theorem fold (ops : Ops) (laneNative laneModel : LaneCall)
 (registryNative registryModel : RegistryCall)
 (lanePacket : ∀ bytes, laneNative bytes = laneModel bytes)
 (registryPacket : ∀ v p ma m r e s, registryNative v p ma m r e s = registryModel v p ma m r e s)
 (program : solana_pubkey.Pubkey) (accounts : Slice Account)
 (pool : solana_pubkey.Pubkey) (lane : U8) (slot : U64) :
 NMX_Emitted.auth ops laneNative registryNative program accounts pool lane slot =
 NMX_Emitted.auth ops laneModel registryModel program accounts pool lane slot := by
 have lanes : laneNative = laneModel := funext lanePacket
 have registries : registryNative = registryModel := by
  funext v p ma m r e s
  exact registryPacket v p ma m r e s
 rw [lanes,registries]
#print fold
#print axioms fold
end NMX_DirectValueFold
end
