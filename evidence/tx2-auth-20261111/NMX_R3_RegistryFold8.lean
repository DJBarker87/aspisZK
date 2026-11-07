import NMX_R3_RegistryFold9
import NMX_R3_RegistryDecoder008
import LIBB_PoolLib
set_option autoImplicit false
noncomputable section
namespace NMX_R3_RegistryFold8
open Aeneas Aeneas.Std AdapterRw NND_Carrier NMX_R3_RegistryEffects

def tail (D : RSL.DeployedIds) (a : RSL.TX2_234.Args) (b : RSL.Bytes) : RSL.RS Unit :=
 RSL.RS.bind (RSL.RS.ofOption (LIBB_PoolLib.library.decodeEntryV2 b) .invalidAccountData)
  (NMX_R3_RegistryFold9.tail D a)

theorem fold (base : Ops) (D : RSL.DeployedIds) (env : RSL.Env)
 (v p : solana_pubkey.Pubkey) (m : r1_pool_adapter.owned.OwnedAccount)
 (s : aspis_statement.pool_v1.pair_forest_accounts.PoolV1PairForestMasterV1)
 (reg ent : r1_pool_adapter.owned.OwnedAccount) (t : U64) (b : Slice U8) :
 RSL.Spec.map (reply id)
  (eval (NMX_R3_RegistryScriptParts.script008 (NMX_R3_RegistryOps.install base D env)
   v ent t (unkey RSL.LOADER_ID) (unkey RSL.LOADER_ID) m.key (unkey D.registry) b)) =
 tail D (NMX_R3_RegistryArgs.args v p m s reg ent t) (bytes b) := by
 rw [NMX_R3_RegistryDecoder008.source]
 apply (NMX_R3_RegistryDecoderLaw.fold (NCX_Install.op34 b)
  (LIBB_V2DecoderTotal.entry b) entryV2 _
  (NMX_R3_RegistryFold9.tail D (NMX_R3_RegistryArgs.args v p m s reg ent t))
  (fun e => NMX_R3_RegistryFold9.fold base D env v p m s reg ent t e)).trans
 rw [←LIBB_V2DecoderValues.entry_bytes b]
 rfl
#print axioms fold
end NMX_R3_RegistryFold8
end
