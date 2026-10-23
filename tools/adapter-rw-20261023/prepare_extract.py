#!/usr/bin/env python3
from pathlib import Path
import json,subprocess
H=Path(__file__).resolve().parent;E=H.parent/'codex-cx-s2e-20261023'
old=json.loads((E/'charon-004.json').read_text())
cmd=[old['command'][0],'cargo','--preset','aeneas','--mir','built','--sysroot','default','--opaque','crate','--opaque','aspis_core','--opaque','aspis_statement','--opaque','aspis_r1_cost_probe','--opaque','solana_program_error']
owned='crate::r1_pool_adapter::owned::'
functions=['stage1_owned','stage2_owned','validate_asq8','authenticate_asq8_accounts','authenticate_invariant_release_registry','require_readonly_buffer','require_readonly_account','require_verifier_checkpoint','require_distinct_accounts','require_zero','{OwnedAccount}::key','{OwnedAccount}::owner','{OwnedAccount}::data','{OwnedAccount}::data_len']
# Both callers are roots; all owned metadata/authentication callees included.
for name in functions:
 cmd+=['--start-from',owned+name,'--include',owned+name]
cmd+=['--start-from','crate::observer','--include','crate::observer']
# Reuse the predecessor's exact protocol value-layout allowlist, not its body.
c=old['command'];allow=[]
for i in range(len(c)-1):
 if c[i]=='--include' and not c[i+1].startswith('crate::S2E_Reference'):
  allow.append(c[i+1])
allow+=['crate::r1_pool_adapter::owned::OwnedAccount','crate::r1_pool_adapter::AuthenticatedAsq8Accounts','crate::r1_pool_adapter::ValidatedAsqa','crate::r1_pool_adapter::ScannedAsqaProof','solana_pubkey::Pubkey','solana_pubkey::PubkeyError','aspis_statement::pool_v1::pair_forest_accounts::PoolV1PairForestMasterV1','aspis_statement::pool_v1::pair_forest_accounts::PoolV1PairForestCheckpointV1','aspis_statement::pool_v1::pair_forest_accounts::PoolV1PairForestLaneStateV1','aspis_statement::pool_v1::verifier_registry::VerifierRegistryV1','aspis_statement::pool_v1::verifier_registry::VerifierRegistryV2','aspis_statement::pool_v1::verifier_registry::VerifierRegistryEntryV1','aspis_statement::pool_v1::verifier_registry::VerifierRegistryEntryV2','aspis_statement::pool_v1::verifier_registry::PoolV1VerifierRegistryFormatError','aspis_statement::pool_v1::pool_identity::PoolIdentityV1','aspis_statement::pool_v1::verifier_policy::VerifierPolicyV1','aspis_statement::pool_v1::incremental_merkle::IncrementalMerkleTreeV1']
for name in dict.fromkeys(allow):cmd+=['--include',name]
cmd+=['--dest-file',str(H/'AdapterRw.llbc'),'--','--manifest-path',str(H/'src/programs/r1-cost-probe/Cargo.toml'),'--features','pool-adapter,private-leaf-salts','--offline','--release','--lib','--jobs','1']
x={**old,'attempt':'charon-001','command':cmd,'sources':['src/programs/r1-cost-probe/src/r1_pool_adapter_owned.rs','src/programs/r1-cost-probe/src/r1_pool_adapter.rs','src/programs/r1-cost-probe/src/lib.rs','src/programs/r1-cost-probe/Cargo.toml','src/Cargo.lock'],'source_revision':'572236f37d','deps_fingerprint':{'scope':'actual candidate source; candidate-sources.json + exact Cargo.lock; existing value/layout allowlist only, child bodies opaque'},'timeout':300}
x['env']['CARGO_TARGET_DIR']=str(H/'charon-target');(H/'charon-001.json').write_text(json.dumps(x,indent=2)+'\n')
