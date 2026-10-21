#!/usr/bin/env python3
from pathlib import Path
import hashlib,json,re,subprocess
E=Path(__file__).resolve().parent.parent
ROOT=Path.cwd(); L=ROOT/'docs/research/v8-r0-zk-20261009/lean'
rows=[json.loads(l) for p in sorted((E/'lean').glob('attempts-*.jsonl')) for l in p.read_text().splitlines()]
accepted=[r for r in rows if r['accepted']]
mods={r['module']:r for r in accepted}
assert len(mods)==5,mods.keys()
allowed={'propext','Classical.choice','Quot.sound'}
for r in rows:
 snap=E/'lean/sources'/('attempt-'+str(r['attempt'])+'-'+Path(r['module']).stem+'.lean.txt')
 assert hashlib.sha256(snap.read_bytes()).hexdigest()==r['source_sha256']
 if not r['accepted']:continue
 assert r['exit_status']==0 and r['swaps']==0 and r['peak_rss_kib']<8*1024**2
 assert r['axioms']
 for a in r['axioms']:
  if 'does not depend' in a:continue
  names=set(re.search(r'\[([^]]*)\]',a,re.S)[1].replace('\n','').replace(' ','').split(','))
  assert names<=allowed,(r['attempt'],names)
for m,r in mods.items():assert hashlib.sha256((L/m).read_bytes()).hexdigest()==r['source_sha256']
changes=subprocess.check_output(['git','diff','--name-status','d9c3ed7ab'],text=True).splitlines()
assert all(x.startswith('A\t') for x in changes),changes
for r in json.loads((E/'rust-attempts.json').read_text()):
 assert r['accepted'] and r['exit_status']==0 and r['swaps']==0
 assert r['limits']=={'memory.high':'6442450944','memory.max':'8589934592','memory.swap.max':'0','pids.max':'64'}
 assert r['env']['RUSTFLAGS']=='-C link-arg=-Wl,--threads=4'
probe=json.loads((E/'sampler16-evidence.json').read_text())
assert probe['exit']==0 and 'source_sampler_accepts_both\\\":true' not in probe['stdout'] # JSON is unescaped after decoding
assert json.loads(probe['stdout'])['source_sampler_accepts_both']
for p in probe['source_tree']:assert hashlib.sha256((ROOT/p['path']).read_bytes()).hexdigest()==p['sha256']
assert not list(ROOT.glob('target'))
result=dict(revision=subprocess.check_output(['git','rev-parse','HEAD'],text=True).strip(),
 accepted_attempts=[r['attempt'] for r in accepted],excluded_attempts=[r['attempt'] for r in rows if not r['accepted']],
 final_audit_axioms=len(mods['R1Z/ProverCommit16Audit.lean']['axioms']),all_changes_additive=True,
 production_source_changes=False,shipped_privacy='target not yet established')
(E/'audit.json').write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps(result))
