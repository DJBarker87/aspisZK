from pathlib import Path
import hashlib,json,re,subprocess
E=Path(__file__).resolve().parent.parent
L=Path('docs/research/v8-r0-zk-20261009/lean')
rows=[]
for p in sorted((E/'lean').glob('attempts-*.jsonl')):
 rows += [json.loads(line) for line in p.read_text().splitlines()]
by={}
allowed={'propext','Classical.choice','Quot.sound'}
for r in rows:
 a=r['attempt'];assert a not in by,a;by[a]=r
 snap=E/'lean/sources'/('attempt-'+str(a)+'-'+Path(r['module']).stem+'.lean.txt')
 assert hashlib.sha256(snap.read_bytes()).hexdigest()==r['source_sha256'],a
 assert r['deps_fingerprint']==hashlib.sha256(json.dumps([tuple(x) for x in r['deps']],sort_keys=True).encode()).hexdigest(),a
 assert r['swaps']==0,a
 if r['accepted']:
  for line in r['axioms']:
   match=re.search(r'depends on axioms: \[([^\]]*)\]',line,re.S)
   if match:assert set(re.findall(r'[A-Za-z_.]+',match[1]))<=allowed,(a,line)
for m in ['R1Z/ProverCommitLowDigits26.lean','R1Z/ProverCommitQuery26.lean',
          'R1Z/ProverCommitQueryTotal26.lean','R1Z/ProverCommitSemanticTransport26.lean',
          'R1Z/ProverCommitDigest26.lean','R1Z/ProverCommitOracleEffect26.lean',
          'R1Z/ProverCommit26Audit.lean']:
 latest=max((r for r in rows if r['module']==m),key=lambda r:r['attempt'])
 assert latest['accepted'],m
 assert hashlib.sha256((L/m).read_bytes()).hexdigest()==latest['source_sha256'],m
 source=(L/m).read_text()
 assert not re.search(r'\b(sorry|admit|native_decide)\b|^axiom\b|set_option max(?:RecDepth|Heartbeats)',source,re.M),m
assert set(by)==set(range(7584,7636))-{7591}
assert len(by[7635]['axioms'])==40
identities=json.loads((E/'rust-inputs.json').read_text())
for name,row in identities.items():
 if row.get('source_snapshot'):
  assert hashlib.sha256(Path(row['source_snapshot']).read_bytes()).hexdigest()==row['source_sha256'],name
rust=[]
for p in sorted((E/'receipts').glob('*/receipt.json')):
 r=json.loads(p.read_text());r['name']=p.parent.name
 assert r['swaps']==0,r['name']
 assert r['limits']=={'memory.high':'6442450944','memory.max':'8589934592','memory.swap.max':'0','pids.max':'64'},r['name']
 rust.append({k:r[k] for k in ['name','exit_status','wall_seconds','peak_rss_kib','swaps','cgroup_memory_peak_bytes']})
for n in range(23): assert next(r for r in rust if r['name']==f'contains-fixed{n}-v1')['exit_status']==0
for n in ['cell-v1','limbs-v2','query-iterator-v1','query-decoder-v1','query-driver-v1','oracle-effect-v1']:
 assert next(r for r in rust if r['name']==n)['exit_status']==0
changed=subprocess.check_output(['git','diff','--name-only','57ca9c452','HEAD'],text=True).splitlines()
assert not any(p.startswith(('crates/','programs/')) for p in changed)
result=dict(status='target not yet established',source_revision=subprocess.check_output(['git','rev-parse','HEAD'],text=True).strip(),
 final_audit=by[7635],lean_attempts=len(rows),lean_passes=sum(r['accepted'] for r in rows),
 lean_failures=[r['attempt'] for r in rows if not r['accepted']],preflight_only=[7591],rust=rust,
 source_effect_obstruction='Native CoinOracle has a RefCell cursor; current extracted Digest32 has no updated oracle/heap state. No unconditional stateless interpretation.',
 endpoint_specialized=False,refinement_premises_removed=0,shipped_files_changed=False)
(E/'final-audit.json').write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps({k:result[k] for k in ['status','lean_attempts','lean_passes','lean_failures','endpoint_specialized']}))
