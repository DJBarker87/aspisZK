"""Validate retained evidence; do not rerun unchanged compiler or runtime gates."""
from pathlib import Path
import re,json,hashlib,subprocess
E=Path(__file__).resolve().parent.parent;D=Path('docs/research/v8-r0-zk-20261009/lean');base='ec5946193'
sha=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest()
rows=[json.loads(line) for p in sorted((E/'lean').glob('attempts-*.jsonl')) for line in p.read_text().splitlines()]
assert sorted(x['attempt'] for x in rows)==list(range(8733,8748))
allowed={'propext','Classical.choice','Quot.sound'}
for x in rows:
 snapshots=list((E/'lean/sources').glob('attempt-'+str(x['attempt'])+'-*.lean.txt'));assert len(snapshots)==1
 assert sha(snapshots[0])==x['source_sha256'] and x['source_revision'] and x['deps_fingerprint'] and x['swaps']==0
 if x['accepted']:
  assert not x['errors'] and x['exit_status']==0
  for ax in x['axioms']:
   if 'depends on axioms:' in ax:assert set(n.strip() for n in ax.split('[')[1].split(']')[0].replace('\n','').split(','))<=allowed
final=next(x for x in rows if x['attempt']==8747);assert final['accepted'] and len(final['axioms'])==24
modules=['ProverCommitTablePrefix21','ProverCommitKeyCompare21','ProverCommitTableKeys21','ProverCommitNonzeroStream21','ProverCommitTail21']
for m in modules:
 p=D/'R1Z'/(m+'.lean');s=p.read_text()
 assert not re.search(r'\b(sorry|admit|axiom|native_decide)\b',s)
 assert not re.search(r'set_option (maxRecDepth|maxHeartbeats)',s)
 accepted=[x for x in rows if x['module']=='R1Z/'+m+'.lean' and x['accepted']];assert sha(p)==accepted[-1]['source_sha256']
 for n in re.findall(r'^theorem (\w+)',s,re.M):assert any("'R1Z."+m+'.'+n+"'" in a for a in final['axioms'])
for x in json.loads((E/'extraction/control21/promotion.json').read_text())['files']:
 assert sha(E/'extraction/control21'/(x['file']+'.txt'))==x['raw_sha256']
 assert sha(D/'AspisR1SimControl21'/x['file'])==x['promoted_sha256']
 assert not re.search(r'^axiom ',(D/'AspisR1SimControl21'/x['file']).read_text(),re.M)
changed=subprocess.check_output(['git','diff',base,'--name-only'],text=True).splitlines()
assert not any(p.startswith(('crates/','programs/')) for p in changed)
assert not any(any(n in p for n in ['SourceIdentification','RustRuntimeJoin','PrivacyR1FinalRelease']) for p in changed)
assert not any(p.endswith(('.olean','.elf','.llbc','.so','.tar','.gz')) for p in changed)
endpoint=D/'R1Z/PrivacyR1HeadlineDeployed.lean'
assert subprocess.check_output(['git','show',base+':'+str(endpoint)])==endpoint.read_bytes()
rust=json.loads((E/'rust-attempts.json').read_text())
for x in rust:
 assert x['swaps']==0 and x['limits']=={'memory.high':'6442450944','memory.max':'8589934592','memory.swap.max':'0','pids.max':'64'}
 if x['accepted']:
  assert x['exit_status']==0
  out=(E/'receipts'/x['name']/'stdout.log').read_text()
  if x['name']=='tail-runtime-v1':assert 'test result: ok. 2 passed' in out
  elif not x['name'].startswith('sim-tail-control-v2-'):assert 'VERIFICATION:- SUCCESSFUL' in out
packet=dict(base_revision=base,source_revision=subprocess.check_output(['git','rev-parse','HEAD'],text=True).strip(),packet_valid=True,formal_target_established=False,lean_attempts=len(rows),next_env_J_attempt=8748,final_audit={k:final[k] for k in ['module','attempt','source_sha256','deps_fingerprint','source_revision','exit_status','wall_time','peak_rss_kib','swaps','axioms']},accepted_rust=[x['name'] for x in rust if x['accepted']],endpoint_unchanged=True,endpoint_sha256=sha(endpoint),shipped_sources_unchanged=True,frozen_ELFs='Reuse D129 exactly unchanged shipped source evidence; no rebuild or new equivalence claim',release_replay='Withheld: universal source closure remains open; this is a focused changed-cone axioms audit against accepted cached dependencies',source_binding='source-prefix-binding.json records inherited host-only coin18 projection and exact hashes')
(E/'final-audit.json').write_text(json.dumps(packet,indent=2)+'\n')
print(json.dumps({k:packet[k] for k in ['packet_valid','formal_target_established','lean_attempts','next_env_J_attempt','shipped_sources_unchanged']}))
