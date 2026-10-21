"""Validate exact source snapshots, receipts, source ports and final closure."""
from pathlib import Path
import subprocess,re,json,hashlib
E=Path(__file__).resolve().parent.parent
L=Path('docs/research/v8-r0-zk-20261009/lean')
rows=[]
for p in sorted((E/'lean').glob('attempts-*.jsonl')):rows += [json.loads(x) for x in p.read_text().splitlines()]
by={}
for r in rows:
 a=r['attempt'];assert a not in by,a;by[a]=r
 snap=E/'lean/sources'/('attempt-'+str(a)+'-'+Path(r['module']).stem+'.lean.txt')
 assert hashlib.sha256(snap.read_bytes()).hexdigest()==r['source_sha256'],a
 assert hashlib.sha256(json.dumps([tuple(x) for x in r['deps']],sort_keys=True).encode()).hexdigest()==r['deps_fingerprint'],a
 assert r['swaps']==0,a
 if r['accepted']:
  for line in r['axioms']:
   match=re.search(r'depends on axioms: \[([^\]]*)\]',line,re.S)
   if match:assert set(re.findall(r'[A-Za-z_.]+',match[1])) <= {'propext','Classical.choice','Quot.sound'},(a,line)
assert set(by)==set(range(7800,7834))
assert by[7831]['accepted'] and len(by[7831]['axioms'])==35
modules=[str(p.relative_to(L)) for p in (L/'R1Z').glob('ProverCommit*28*.lean')]
modules += [f'AspisR1SemanticInit28/{q}.lean' for q in ['Types','FunsExternal','Funs']]
latest={}
for m in modules:
 r=max((r for r in rows if r['module']==m),key=lambda r:r['attempt']);assert r['accepted'],m
 p=L/m;assert hashlib.sha256(p.read_bytes()).hexdigest()==r['source_sha256'],m
 assert not re.search(r'\b(sorry|admit|native_decide)\b|^axiom\b',p.read_text(),re.M),m
 if m.startswith('R1Z/') or m.endswith('FunsExternal.lean'):
  assert not re.search(r'set_option max(?:RecDepth|Heartbeats)',p.read_text()),m
 latest[m]=r['attempt']
closure=json.loads((E/'closure-check.json').read_text());assert not closure['mismatches']
assert closure['preflight_7834']['deps_fingerprint']==by[7816]['deps_fingerprint']
assert closure['preflight_7834']['source_sha256']==by[7816]['source_sha256']
rust=[]
for p in sorted((E/'receipts').glob('*/receipt.json')):
 r=json.loads(p.read_text());name=p.parent.name
 assert r['swaps']==0,name
 assert r['limits']=={'memory.high':'6442450944','memory.max':'8589934592','memory.swap.max':'0','pids.max':'64'},name
 assert r['env']['RUSTFLAGS']=='-C link-arg=-Wl,--threads=4 --cfg aeneas_ref',name
 rust.append(dict(name=name,**{k:r[k] for k in ['exit_status','wall_seconds','peak_rss_kib','swaps','cgroup_memory_peak_bytes']}))
for name in ['init28-v2-charon','init28-v2-aeneas','walk28-v1-charon']:
 assert next(r for r in rust if r['name']==name)['exit_status']==0,name
assert next(r for r in rust if r['name']=='walk28-v1-aeneas')['exit_status']==2
for script in ['port-control.py','port-semantic.py']:
 subprocess.run(['python3',str(E/'harness'/script),'--check'],check=True)
changed=subprocess.check_output(['git','diff','--name-only','26b922be6'],text=True).splitlines()
assert not any(p.startswith(('crates/','programs/')) for p in changed)
identity=json.loads((E/'endpoint-identity.json').read_text());assert identity['byte_identical'] and identity['refinement_premises_removed']==0
assert not (E/'endpoint-deletion.diff').read_bytes()
for label in ['before','after']:
 assert hashlib.sha256((E/('endpoint-'+label+'.lean.txt')).read_bytes()).hexdigest()==identity[label+'_sha256']
result=dict(status='target not yet established',source_revision=subprocess.check_output(['git','rev-parse','HEAD'],text=True).strip(),source_base_revision='26b922be6',
 final_axioms_audit=by[7831],latest_sources=latest,lean_attempts=len(rows),lean_passes=sum(r['accepted'] for r in rows),
 excluded_lean=[r['attempt'] for r in rows if not r['accepted']],preflight_only=[7834],preflight_reason='Unchanged source/deps refused; no compiler launched. Subsequent targets were not rerun.',rust=rust,
 source_scope='Kernel-checked pure reconstruction and concrete stateful installation of retained semantic/circle/control continuations; ordered observer, replay reset, port marginals, actual initializer and constructed complete formal walk.',
 obstruction='Native sim::walk iterator/borrow join fails Aeneas InterpJoin.ml:2209 at sim.rs:165-177. Native loop-shell to bounded row-continuation source equation and outer attempt assembly remain open.',
 shipped_prover_experiment_constructed=False,whole_run_joins_constructed=False,endpoint_specialized=False,refinement_premises_removed=0,shipped_files_changed=False)
(E/'final-audit.json').write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps({k:result[k] for k in ['status','lean_attempts','lean_passes','excluded_lean','endpoint_specialized']}))
