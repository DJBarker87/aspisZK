#!/usr/bin/env python3
"""Read-only validation of adopted source/evidence; never reruns a compiler."""
from pathlib import Path
import difflib,hashlib,json,re,subprocess,sys
assert sys.argv[1:]==['--check']
E=Path(__file__).resolve().parent.parent
L=Path('docs/research/v8-r0-zk-20261009/lean/R1Z')
m=json.loads((E/'manifest.json').read_text())
for name,sha in m['sources'].items():
 p=Path(name);assert hashlib.sha256(p.read_bytes()).hexdigest()==sha,name
 if p.suffix=='.lean':
  s=p.read_text();assert not re.search(r'\b(sorry|axiom|admit|native_decide)\b',s),name
  assert not re.search(r'set_option (maxRecDepth|maxHeartbeats)',s),name
before=(E/'headline-specialized-before.lean.txt').read_text()
after=(E/'headline-specialized-after.lean.txt').read_text()
assert after==(L/'ProverCommitFixedEndpoint.lean').read_text()
diff=''.join(difflib.unified_diff(before.splitlines(True),after.splitlines(True),fromfile='specialized-before',tofile='specialized-after'))
assert diff==(E/'headline-deletions.diff').read_text()
assert diff and not any(l.startswith('+') and not l.startswith('+++') for l in diff.splitlines())
assert before[before.index(' :\n    ZK_FSS'):]==after[after.index(' :\n    ZK_FSS'):]
old='docs/research/v8-r0-zk-20261009/lean/R1Z/ProverCommitAdmittedEndpoint.lean'
assert Path(old).read_bytes()==subprocess.check_output(['git','show','542fe958f:'+old])
rows=[]
for p in sorted((E/'lean').glob('attempts-*.jsonl')):
 for line in p.read_text().splitlines():
  r=json.loads(line);rows.append(r)
  snapshot=E/'lean/sources'/('attempt-'+str(r['attempt'])+'-'+Path(r['module']).stem+'.lean.txt')
  assert hashlib.sha256(snapshot.read_bytes()).hexdigest()==r['source_sha256']
  assert r['swaps']==0
  if r['accepted']:
   assert r['exit_status']==0 and not r['errors']
   for ax in r['axioms']:
    found=re.search(r'\[([^]]*)\]',ax)
    if found:assert set(re.findall(r'[\w.]+',found[1]))<={'propext','Classical.choice','Quot.sound'},ax
assert sorted(r['attempt'] for r in rows)==m['assigned_attempts_consumed']
final=next(r for r in rows if r['attempt']==8399)
assert final['accepted'] and len(final['axioms'])==40
for name in ['ProverCommitFixedObserver','ProverCommitFixedEndpoint','ProverCommitMaterialPrefix']:
 last=max((r for r in rows if r['module']=='R1Z/'+name+'.lean'),key=lambda r:r['attempt'])
 assert last['accepted'] and last['source_sha256']==hashlib.sha256((L/(name+'.lean')).read_bytes()).hexdigest()
for r in json.loads((E/'rust-attempts.json').read_text()):
 assert r['accepted'] and r['exit_status']==0 and r['swaps']==0
 assert r['limits']=={'memory.high':'6442450944','memory.max':'8589934592','memory.swap.max':'0','pids.max':'64'}
 assert r['env']['RUSTFLAGS']=='-C link-arg=-Wl,--threads=4'
 output=(E/'receipts'/r['name']/'stdout.log').read_text()
 assert 'VERIFICATION:- SUCCESSFUL' in output
 assert '1 successfully verified harnesses, 0 failures, 1 total' in output
 pins=json.loads((E/(r['name']+'-inputs.json')).read_text())
 assert sum(x['bytes'] for x in pins['reservations'])+8*2**30<=55*2**30
 for name in ['state_only_hiding.rs','prover_commit_reference.rs']:
  assert hashlib.sha256((E/'rust-sources'/name).read_bytes()).hexdigest()==pins['source_hashes']['crates/aspis-prover/src/'+name]
assert (E/'rust-sources/state_only_hiding.rs').read_text().split('\n#[cfg(kani)]\n')[0]==Path('crates/aspis-prover/src/state_only_hiding.rs').read_text().split('\n#[cfg(kani)]\n')[0]
assert (E/'rust-sources/prover_commit_reference.rs').read_text().startswith(Path('crates/aspis-prover/src/prover_commit_reference.rs').read_text())
assert len(json.loads((E/'kani-artifacts.json').read_text()))==1
assert m['fixed_observer_model_joins_closed']
assert not any(v for k,v in m.items() if k.endswith('_closed') and k!='fixed_observer_model_joins_closed')
for p in E.rglob('*'):
 if p.is_file():assert p.suffix not in ['.olean','.llbc','.bin','.elf','.tar','.gz'],p
print('PASS: source pins, deletion-only specialization, 40 final accepted axiom audits, candidate-step receipt, proof-only Rust prefix, explicit source obligations')
