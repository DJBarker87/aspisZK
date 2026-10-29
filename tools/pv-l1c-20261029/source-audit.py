"""Pin and inspect the actual client roots. Source evidence, not native refinement."""
from pathlib import Path
import subprocess,hashlib,json
E=Path('evidence/pv-l1c-20261029');rev=subprocess.check_output(['git','rev-parse','HEAD'],text=True).strip()
paths=['tools/r1-cost-probe/src/bin/devnet_spend/plan.rs','tools/r1-cost-probe/src/bin/devnet_spend/Client64_accounts.rs','tools/r1-cost-probe/src/bin/devnet_spend.rs']
files={}
for p in paths:
 b=subprocess.check_output(['git','show',rev+':'+p]);files[p]=dict(revision=rev,path=p,git_blob=subprocess.check_output(['git','rev-parse',rev+':'+p],text=True).strip(),sha256=hashlib.sha256(b).hexdigest(),size=len(b),text=b.decode())
def locate(p,s):
 t=files[p]['text'];assert t.count(s)==1,(p,s,t.count(s));start=t.index(s);return dict(path=p,line=t[:start].count('\n')+1,exact=s)
p=paths[0];a=paths[1]
entries={
 'clock_start':locate(p,'let started=Instant::now();'),
 'clock_finish_and_JSON':locate(p,'"prove_wall_seconds":started.elapsed().as_secs_f64()'),
 'same_result_count':locate(p,'"attempts":result.attempts'),
 'selected_account':locate(p,'accounts.selected(result.attempts)?'),
 'selected_index_formula':locate(a,'Ok((attempts - 1, self.keys[attempts - 1]))'),
 'selected_count_validation':locate(a,'ensure!((1..=CAP).contains(&attempts) && attempts == self.entered, "invalid successful attempt count");'),
 'proof_upload_count':locate(p,'"proof_upload_count":proof.len().div_ceil(3763)'),
 'statement_upload_count':locate(p,'"statement_upload_count":1'),
 'publication_same_count':locate(p,'accounts.publication(result.attempts,&mut a,pk(q,"public_account"),pk(q,"verifier_checkpoint"))?'),
 'proof_account_route':locate(p,'RealR1_client::prove_for_proof_accounts(statement.semantic_public(),&compiled,HOST_HASH,&mut store,|k| accounts.nonce(k))'),
 'stdout':locate(paths[2],'println!("{}",plan::run(&q)?)'),
 'durable_store':locate(p,'DurableStateOnlyMaskNonceStore::open(dir.join("mask-nonce-ledger"))?'),
}
assert entries['clock_start']['line']<entries['durable_store']['line']<entries['clock_finish_and_JSON']['line']
for f in files.values():f.pop('text')
out=dict(source_revision=rev,files=files,sites=entries,evidence_class='mechanically checked source spellings and ordering only; no structural binding or compiled-artifact claim',timing_dependency='D359 owner timing-evidence decision for throttled-host measurements, pending; not assumed',runtime_boundary='rdea-1 allocator success/failure/prefix on public request words; native argument provenance, ownership/address observations and cross-channel coupling remain open',compiler_boundary='V370, D381/D386 pending',deployed_configuration_required_but_not_executed=dict(toolchain='1.94.1',features=['r1p-check','aspis-r1-cost-probe/ct-host-prover'],profile='release',lockfile='deployed Cargo.lock'))
(E/'source-audit.json').write_text(json.dumps(out,indent=2)+'\n');print('Pinned client roots:',len(files),'checked sites:',len(entries))
