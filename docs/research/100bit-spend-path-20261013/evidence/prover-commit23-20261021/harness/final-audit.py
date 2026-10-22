"""Verify final focused evidence, source identities, axioms and scope."""
from pathlib import Path
import json,hashlib,re,subprocess
E=Path(__file__).resolve().parent.parent
D=Path('docs/research/v8-r0-zk-20261009/lean/R1Z')
base='cb9372b8f'
sha=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest()
rows=[json.loads(l) for p in sorted((E/'lean').glob('attempts-*.jsonl')) for l in p.read_text().splitlines()]
assert sorted(r['attempt'] for r in rows)==list(range(7474,7487))
allowed={'propext','Classical.choice','Quot.sound'}
for r in rows:
 snap=list((E/'lean/sources').glob('attempt-'+str(r['attempt'])+'-*.lean.txt'))
 assert len(snap)==1 and sha(snap[0])==r['source_sha256']
 assert r['source_revision'] and r['deps_fingerprint'] and r['swaps']==0
 assert r['memory_limit_mib']==7000 and r['cgroup_memory_max_gib']==8
 assert r['accepted']==(r['exit_status']==0)
 if r['accepted']:
  assert not r['errors']
  for a in r['axioms']:
   if 'depends on axioms:' in a:
    assert set(n.strip() for n in a.split('[')[1].split(']')[0].replace('\n','').split(','))<=allowed
final=next(r for r in rows if r['attempt']==7486)
assert final['accepted'] and len(final['axioms'])==24
mods=['ProverCommitTLS23','ProverCommitTreeOps23','ProverCommitAdaptiveFuel23','ProverCommitAdaptiveLaw23','ProverCommitAdaptiveHistory23','ProverCommitPolicy23','ProverCommit23Audit']
for m in mods:
 p=D/(m+'.lean');s=p.read_text()
 assert not re.search(r'\b(sorry|admit|axiom|native_decide)\b',s)
 assert not re.search(r'set_option (maxRecDepth|maxHeartbeats)',s)
 accepted=[r for r in rows if r['module']=='R1Z/'+m+'.lean' and r['accepted']]
 assert sha(p)==accepted[-1]['source_sha256']
 for name in re.findall(r'^theorem (\w+)',s,re.M):
  assert any("'R1Z."+m+'.'+name+"'" in a for a in final['axioms'])
rust=json.loads((E/'rust-attempts.json').read_text());assert len(rust)==8
assert {r['name'] for r in rust if r['accepted']}=={'tls-single-v2','tls-programmed-v1','tree-get-v1','tree-iter-v1'}
for r in rust:
 assert r['swaps']==0 and r['limits']=={'memory.high':'6442450944','memory.max':'8589934592','memory.swap.max':'0','pids.max':'64'}
 assert r['env']['RUSTFLAGS']=='-C link-arg=-Wl,--threads=4'
 assert r['source_revision']==base and r['peak_rss_kib'] and r['wall_seconds']
 assert r['accepted']==('VERIFICATION:- SUCCESSFUL' in (E/'receipts'/r['name']/'stdout.log').read_text() and r['exit_status']==0)
for p in E.glob('*stop.json'):
 r=json.loads(p.read_text());assert r['memory_current_bytes']>=6*2**30-64*2**20
 assert r['command'].startswith('cbmc ')
binding=json.loads((E/'source-prefix-binding.json').read_text())
for r in binding['files']:assert sha(r['file'])==r['production_sha256']
assert len(binding['rust_inputs'])==8
launcher=(E/'harness/run-joint.sh.txt').read_text()
for s in ['MemoryHigh=$((MX-2))G','MemoryMax=${MX}G','MemorySwapMax=0','TasksMax=64','if [ 0 = 1 ]','/tmp/aspis-r0-lean.lock']:assert s in launcher
changed=subprocess.check_output(['git','diff',base,'--name-only'],text=True).splitlines()
assert not any(p.startswith(('crates/','programs/')) for p in changed)
assert not any(any(n in p for n in ['SourceIdentification','RustRuntimeJoin','PrivacyR1FinalRelease']) for p in changed)
assert not any(p.endswith(('.olean','.elf','.tar','.tar.gz')) for p in changed)
for m in ['PrivacyR1HeadlineDeployed','ProverCommitDeployedFuel22','ProverCommitFuelJoin22']:
 p=D/(m+'.lean');assert p.read_bytes()==subprocess.check_output(['git','show',base+':'+str(p)])
report=Path('docs/research/v8-r0-zk-20261009/r1p-final/PROVER-COMMIT23-20261021.md').read_text()
endpoint=(D/'ProverCommitDeployedFuel22.lean').read_text()
ref=endpoint.split('def RustProverRefinement : Prop :=',1)[1].split('\n\n',1)[0]
statement=endpoint.split('theorem privacy_headline_deployed',1)[1].split(' := by',1)[0]
assert report.count('def RustProverRefinement : Prop :='+ref)==2
assert report.count('theorem privacy_headline_deployed'+statement)==2
packet=dict(base_revision=base,source_revision=final['source_revision'],final_target=final['module'],final_attempt=7486,
 final_result={k:final[k] for k in ['source_sha256','deps_fingerprint','exit_status','wall_time','peak_rss_kib','swaps','axioms']},
 axioms_audits=24,consumed_attempts=list(range(7474,7487)),next_attempt_candidate=7487,
 remaining_range='7487-7499; check receipts before use',accepted_rust=[r['name'] for r in rust if r['accepted']],
 new_top_theorems=20,shipped_files_changed=False,concurrent_owner_files_changed=False,endpoint_unchanged=True,
 source_prefix_binding_checked=True,source_snapshots_checked=True,full_frozen_manifest_replayed=False,
 target_established=False,shippedProverExperiment_constructed=False,WholeRunJoins_constructed=False,
 blockers=['split insertion source formula pressure near MemoryHigh; universal Rust tree representation unproved',
 'concrete marked program/Fresh/counter-room instance and finite coupling marginals',
 'remaining gamma/ordinary/query policies, circle/caller/error/retry/serialization assembly and full native trace join'],
 audit_scope='One focused final changed-cone audit against retained caches; no release closure claim')
(E/'final-audit.json').write_text(json.dumps(packet,indent=2)+'\n')
print('PASS: 20 new theorem audits, 24 final axioms lines, exact sources/receipts/caps, unchanged endpoint and shipped files')
