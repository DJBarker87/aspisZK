"""Exact source inventory and assertions, not source/executable refinement."""
from pathlib import Path
import subprocess,hashlib,json,re
E=Path('evidence/pv-rj4id-20261029');rev=subprocess.check_output(['git','rev-parse','HEAD'],text=True).strip();ref=subprocess.check_output(['git','rev-parse','origin/codex/pv-runjoin-20261026'],text=True).strip()
read=lambda r,p:subprocess.check_output(['git','show',r+':'+p]);sha=lambda b:hashlib.sha256(b).hexdigest()
paths=['tools/r1-cost-probe/src/bin/devnet_spend.rs','tools/r1-cost-probe/src/bin/devnet_spend/plan.rs','tools/r1-cost-probe/src/bin/devnet_spend/Client64_accounts.rs','crates/aspis-r1-cost-probe/src/RealR1_client.rs','crates/aspis-r1-cost-probe/src/prover.rs','crates/aspis-r1-cost-probe/src/prover_powers.rs','crates/aspis-r1-cost-probe/src/lib.rs','crates/aspis-core/src/r0/encoder.rs','crates/aspis-statement/src/pool_v1/pair_forest_terminal.rs','tools/r1-cost-probe/Cargo.toml','tools/r1-cost-probe/Cargo.lock','tools/r1-cost-probe/rust-toolchain.toml','crates/aspis-r1-cost-probe/Cargo.toml']
records=[];texts={}
pattern=r'Runtime|disclosed|observerOracle|plan::run|prove_for_proof_accounts|prove_masked_retrying_with|retry_attempt|opening_claim_bytes|opening_batch|eval_message|prover_powers::powers|semantic_public|Instant|elapsed|fs::write|next_pair_index:|let statement=|let public=|proof_account\(k\)|accounts\.nonce|pub mod prover_powers|ct-host-prover'
for p in paths:
 b=read(rev,p);texts[p]=b.decode();records.append(dict(path=p,revision=rev,git_blob=subprocess.check_output(['git','rev-parse',rev+':'+p],text=True).strip(),sha256=sha(b),lines=[dict(line=i,text=l) for i,l in enumerate(b.decode().splitlines(),1) if re.search(pattern,l)]))
plan=texts[paths[1]];client=texts[paths[3]];prover=texts[paths[4]];powers=texts[paths[5]]
assert not re.search(r'\bRuntime\b',plan+client) and 'disclosed' not in plan+client and 'observerOracle' not in plan+client
assert plan.count('RealR1_client::prove_for_proof_accounts(')==1
assert 'statement.semantic_public(),&compiled,HOST_HASH,&mut store,|k| accounts.nonce(k)' in plan
assert 'r0::encoder::eval_message(&coefficients[lane],z1)' in prover
assert 'crate::prover_powers::powers::<29>(gamma)' in prover
assert powers=='''//! Prover-local op254 copy; release weights::powers remains unchanged.
use aspis_core::field::WideExact as E;

pub fn powers<const N: usize>(x: E) -> [E; N] {
    let mut out = [E::ZERO; N];
    let mut p = E::ONE;
    let mut i = 0usize;
    while i < N {
        out[i] = p;
        i += 1;
        if i < N { p = p.mul(x); }
    }
    out
}
'''
assert 'next_pair_index:lane.tree.next_leaf_index' in plan
assert 'prove_wall_seconds' in plan and 'started.elapsed().as_secs_f64()' in plan
model_paths=['PV_RunJoin_Deployed','PV_RunJoin_SourceConstructor','PV_RunJoin_LedgerConstructor','PV_RunJoin_InstalledEndpoint','PV_RJDec_CommonCases','PV_RJDec_ResultCases','PV_RJDec_V047Native','PV_RunJoin_GammaPowers44','PV_RunJoin_ClaimEvaluator48']
for m in model_paths:
 p='docs/research/v8-r0-zk-20261009/lean/R1Z/'+m+'.lean';b=read(ref,p)
 records.append(dict(path=p,revision=ref,git_blob=subprocess.check_output(['git','rev-parse',ref+':'+p],text=True).strip(),sha256=sha(b),text=b.decode()))
# A source-law disposition is inherited exactly, never upgraded to deployed credit.
row=json.loads(read(rev,'evidence/pv-rdcd-20261028/rows/V201.json'));assert row['status']=='SUSPENDED' and row['deployed_generic_mir_audit']['unresolved_records']==145
native=json.loads(read(rev,'evidence/pv-rdcd-20261028/project-native-inputs.json'))
key='evidence/pv-op254-20261027/native/copy-powers.rs';assert sha(powers.encode())==native[key]['sha256']
(E/'source-audit.json').write_text(json.dumps(dict(revision=rev,runjoin_read_only_revision=ref,records=records,checks='all assertions passed',evidence_class='source inspection and exact text checks; no universal native refinement',V201=row,powers_retained_source_sha256=native[key]['sha256'],observation_finding=False,observation_finding_note='No actual native decoder was identified, so no witness-dependent decoder counterexample is claimed.'),indent=2)+'\n')
print('source audit passed',len(records),'source records; no deployed decoder identification claimed')
