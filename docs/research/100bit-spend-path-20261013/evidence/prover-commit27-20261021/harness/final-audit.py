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
assert set(by)==set(range(7636,7675))-{7661}
assert not by[7673]['accepted']
assert by[7674]['accepted'] and len(by[7674]['axioms'])==34
modules=['R1Z/ProverCommit'+n+'27.lean' for n in ['CoinTape','CursorMarginal','TranscriptTape','ExtractedCoin','CoinCall','CoinSequence','MachineMarginal','EffectCallers','']]
modules[-1]='R1Z/ProverCommit27Audit.lean'
modules += [f'AspisR1{p}27/{q}.lean' for p in ['CoinEffect','EffectCallers'] for q in ['Types','Funs']]
latest={}
for m in modules:
 r=max((r for r in rows if r['module']==m),key=lambda r:r['attempt']);assert r['accepted'],m
 p=L/m;assert hashlib.sha256(p.read_bytes()).hexdigest()==r['source_sha256'],m
 if m.startswith('R1Z/'):
  assert not re.search(r'\b(sorry|admit|native_decide)\b|^axiom\b|set_option max(?:RecDepth|Heartbeats)',p.read_text(),re.M),m
 latest[m]=r['attempt']
rust=[]
for p in sorted((E/'receipts').glob('*/receipt.json')):
 r=json.loads(p.read_text());name=p.parent.name
 assert r['swaps']==0,name
 assert r['limits']=={'memory.high':'6442450944','memory.max':'8589934592','memory.swap.max':'0','pids.max':'64'},name
 assert r['env']['RUSTFLAGS']=='-C link-arg=-Wl,--threads=4',name
 rust.append(dict(name=name,**{k:r[k] for k in ['exit_status','wall_seconds','peak_rss_kib','swaps','cgroup_memory_peak_bytes']}))
for name in ['call-v4','different-v1','extracted-call-v5','read-address115-v1','effect-charon-v4','effect-aeneas-v4','callers-charon-v1','callers-aeneas-v1']:
 assert next(r for r in rust if r['name']==name)['exit_status']==0,name
for p in E.glob('*-inputs.json'):
 r=json.loads(p.read_text())
 if 'sources' in r:
  name=p.name[:-len('-inputs.json')]
  for src,h in r['sources'].items():assert hashlib.sha256((E/'rust-sources'/name/(src+'.txt')).read_bytes()).hexdigest()==h,(name,src)
 for cap in r.get('reservations',[]):assert cap['bytes']<=55*2**30
changed=subprocess.check_output(['git','diff','--name-only','26b922be6','HEAD'],text=True).splitlines()
assert not any(p.startswith(('crates/','programs/')) for p in changed)
identity=json.loads((E/'endpoint-identity.json').read_text());assert identity['byte_identical'] and identity['refinement_premises_removed']==0
assert not (E/'endpoint-deletion.diff').read_bytes()
for label in ['before','after']:
 assert hashlib.sha256((E/('endpoint-'+label+'.lean.txt')).read_bytes()).hexdigest()==identity[label+'_sha256']
result=dict(status='target not yet established',source_revision=subprocess.check_output(['git','rev-parse','HEAD'],text=True).strip(),source_base_revision='26b922be6',
 final_audit=by[7674],latest_sources=latest,lean_attempts=len(rows),lean_passes=sum(r['accepted'] for r in rows),
 excluded_lean=[r['attempt'] for r in rows if not r['accepted']],preflight_only=[7661],rust=rust,
 source_scope='Owned generated state-passing oracle, full generated call-tree induction, product/component marginals and effectful caller skeletons. Bounded native RefCell gates and native 115-word read address identity.',
 obstruction='Retained complete semantic/circle/control continuations require a pure Digest32 dictionary. J7673 rejects direct stateful installation; complete effectful policy/walk/retry/trace/serialization ports and whole-source joins remain open.',
 native115_monolithic_gate='timeout; not verification',shipped_prover_experiment_constructed=False,whole_run_joins_constructed=False,
 endpoint_specialized=False,refinement_premises_removed=0,shipped_files_changed=False)
(E/'final-audit.json').write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps({k:result[k] for k in ['status','lean_attempts','lean_passes','excluded_lean','endpoint_specialized']}))
