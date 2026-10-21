"""Validate exact focused evidence without repeating unchanged builds."""
from pathlib import Path
import json,hashlib,re,subprocess
E=Path(__file__).resolve().parent.parent;D=Path('docs/research/v8-r0-zk-20261009/lean/R1Z');base='d9865ba52'
sha=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest()
rows=[json.loads(l) for p in sorted((E/'lean').glob('attempts-*.jsonl')) for l in p.read_text().splitlines()]
assert sorted(r['attempt'] for r in rows)==list(range(8748,8773))
allowed={'propext','Classical.choice','Quot.sound'}
for r in rows:
 snaps=list((E/'lean/sources').glob('attempt-'+str(r['attempt'])+'-*.lean.txt'));assert len(snaps)==1
 assert sha(snaps[0])==r['source_sha256'] and r['source_revision'] and r['deps_fingerprint'] and r['swaps']==0
 if r['accepted']:
  assert r['exit_status']==0 and not r['errors']
  for a in r['axioms']:
   if 'depends on axioms:' in a:assert set(n.strip() for n in a.split('[')[1].split(']')[0].replace('\n','').split(','))<=allowed
final=next(r for r in rows if r['attempt']==8772);assert final['accepted'] and len(final['axioms'])==42
mods=['ProverCommitFuel22','ProverCommitFuelMass22','ProverCommitFuelJoin22','ProverCommitDeployedFuel22','ProverCommitTreeMap22','ProverCommitSemanticSampler22','ProverCommitCircleSampler22','ProverCommitFuelOracle22','ProverCommit22Audit']
for m in mods:
 p=D/(m+'.lean');s=p.read_text()
 assert not re.search(r'\b(sorry|admit|axiom|native_decide)\b',s)
 assert not re.search(r'set_option (maxRecDepth|maxHeartbeats)',s)
 accepted=[r for r in rows if r['module']=='R1Z/'+m+'.lean' and r['accepted']];assert sha(p)==accepted[-1]['source_sha256']
 for name in re.findall(r'^theorem (\w+)',s,re.M):assert any("'R1Z."+m+'.'+name+"'" in a for a in final['axioms'])
rust=json.loads((E/'rust-attempts.json').read_text());assert len(rust)==3
for r in rust:
 assert r['swaps']==0 and r['limits']=={'memory.high':'6442450944','memory.max':'8589934592','memory.swap.max':'0','pids.max':'64'}
 assert r['source_revision']=='d9865ba52'
assert [r['name'] for r in rust if r['accepted']]==['nonzero-five-v1']
assert 'pthread_key_create' in (E/'receipts/tls-append-v1/stdout.log').read_text()
stop=json.loads((E/'tree-insert-stop.json').read_text());assert stop['memory_current_bytes']>=6*2**30-2**20
binding=json.loads((E/'r4-reuse-binding.json').read_text())
for r in binding['source_ports']:
 assert sha(r['source'])==r['source_sha256'] and sha(r['port'])==r['port_sha256']
for r in binding['shared_source']:assert sha(r['file'])==r['sha256'] and r['identical_to_r4_source_inventory']
cache=json.loads((E/'r4-installed-closure.json').read_text());assert len(cache['selected'])==40 and not cache['missing'] and cache['existing_objects_overwritten']==cache['source_files_overwritten']==0
changed=subprocess.check_output(['git','diff',base,'--name-only'],text=True).splitlines()
assert not any(p.startswith(('crates/','programs/')) for p in changed)
assert not any(any(n in p for n in ['SourceIdentification','RustRuntimeJoin','PrivacyR1FinalRelease']) for p in changed)
assert not any(p.endswith(('.olean','.elf','.tar','.tar.gz')) for p in changed)
for path in ['docs/research/v8-r0-zk-20261009/lean/R1Z/PrivacyR1HeadlineDeployed.lean']:
 assert Path(path).read_bytes()==subprocess.check_output(['git','show',base+':'+path])
(E/'final-audit.json').write_text(json.dumps(dict(source_revision=final['source_revision'],base_revision=base,final_target=final['module'],final_attempt=8772,exit_status=final['exit_status'],wall_time=final['wall_time'],peak_rss_kib=final['peak_rss_kib'],swaps=final['swaps'],axioms_audits=len(final['axioms']),axioms=final['axioms'],consumed_attempts=list(range(8748,8773)),next_attempt=8773,remaining_assigned_range='8773-8799; check receipts before use',source_snapshots_checked=True,unchanged_original_endpoint=True,shipped_files_changed=False,concurrent_owner_files_changed=False,r4_installed_objects=40,full_frozen_manifest_replayed=False,target_established=False,blockers=['Rust BTreeMap representation/source gate near MemoryHigh','Native pthread_key_create unsupported by Kani','Remaining concrete policy/caller/assembly joins','Adaptive shared-oracle fuel/history adapter'],scope='Focused compilation/audit only; concrete shipped experiment and both WholeRunJoins remain unconstructed'),indent=2)+'\n')
print('PASS: exact source snapshots, 42 standard-axiom audits, capped receipts, source pins, no shipped or concurrent-owner changes')
