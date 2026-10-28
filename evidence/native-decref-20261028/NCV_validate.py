from pathlib import Path
import json,hashlib,re,subprocess,tomllib
E=Path(__file__).resolve().parent
rows=[json.loads(l) for l in (E/'NCV_ATTEMPTS.jsonl').read_text().splitlines()]
assert len({r['attempt'] for r in rows})==len(rows)
counts={k:sum(r['kind']==k for r in rows) for k in ['kani','lean','extract']}
assert counts==dict(kani=60,lean=60,extract=10),counts
allowed={'propext','Classical.choice','Quot.sound'}
limits=dict(**{'memory.high':'6442450944','memory.max':'8589934592','memory.swap.max':'0','pids.max':'64'})
classes={};feature_records=0
manifest=tomllib.loads(subprocess.check_output(['git','show','4bb3b3f51e16b4525f1d10336e2b0bcbbd775387:crates/aspis-r1-cost-probe/Cargo.toml'],text=True))
static={'NCV_src/Cargo.lock':subprocess.check_output(['git','show','4bb3b3f51e16b4525f1d10336e2b0bcbbd775387:Cargo.lock']),'NCV_KMX_copy_stubs.patch':Path('evidence/kani-mitig-20261028/KMX_copy_stubs.patch').read_bytes()}
optimized={x.split('/',1)[1] for x in manifest['features']['optimized-terminal'] if x.startswith('aspis-statement/')}
for r in rows:
 assert r['limits']==limits,(r['attempt'],r['limits'])
 assert int(r['swaps'])==0,r['attempt']
 for n,h in r['source_hashes'].items():
  p=E/r['attempt']/'sources'/n
  data=p.read_bytes() if p.exists() else static[n]
  assert hashlib.sha256(data).hexdigest()==h,(r['attempt'],n)
 if r['kind']=='lean' and r['exit_status']==0:
  for line in r['print_axioms']:
   m=re.search(r'depends on axioms: \[([^]]*)\]',line)
   if m:assert set(m.group(1).split(', '))<=allowed,line
 if r['kind']=='kani':
  a=r['attempt'];g=json.loads((E/(a+'-graph.json')).read_text())
  assert g['graph_matches_frozen'] and g['lock_unchanged'] and g['offline'],a
  assert g['lock_before_sha256']==g['lock_after_sha256']=='5782e6a32026fdd95d252d0db7ea20b16716e6deb4f5a397e744886bb6ba22ef'
  pf={p['name']:set(g['features'][i]) for i,p in g['packages'].items()}
  assert {'pool-adapter','private-leaf-salts'}<=pf['aspis-r1-cost-probe-program']
  assert 'no-entrypoint' not in pf['aspis-r1-cost-probe-program']
  assert {'default','private-leaf-salts','optimized-terminal','program-build'}<=pf['aspis-r1-cost-probe']
  assert {'r0','pool-v1-kernel'}|optimized <= pf['aspis-statement']
  feature_records+=1
  log=(E/a/'stdout.log').read_text()
  if 'CBMC timed out' in log:c='timeout_no_credit'
  elif 'Failed to match the following harness' in log:c='wrong_target_no_credit'
  elif r['exit_status']==0:c='local_positive'
  elif 'Failed Checks:' in log and ' ** 1 of' in log:c='intended_negative'
  else:c='compiler_or_setup_no_credit'
  classes[a]=c
for n,v in json.loads((E/'NCV_DELIVERY.json').read_text()).items():assert hashlib.sha256(Path(n).read_bytes()).hexdigest()==v['source_sha256']
audit=json.loads((E/'NCV_L060/receipt.json').read_text());assert audit['exit_status']==0 and len(audit['print_axioms'])==117
post=json.loads((E/'NCV_POSTFLIGHT.json').read_text());assert not any(post[k] for k in ['source_errors','missing','library_errors','cache_errors'])
assert not list(E.rglob('NCV_ACTIVE.json'))
assert not [str(p) for p in E.rglob('*') if p.is_file() and p.stat().st_size>20*1024*1024]
out=dict(counts=counts,kani_classes=classes,kani_totals={c:list(classes.values()).count(c) for c in sorted(set(classes.values()))},deployed_feature_records=feature_records,optimized_statement_features=sorted(optimized),audit=dict(exit=0,wall=audit['wall_seconds'],peak_rss_kib=audit['peak_rss_kib'],swaps=audit['swaps'],axiom_lines=len(audit['print_axioms']),all_standard=True),frozen_paths=post['frozen_paths'],validation='PASS; no complete native decoder or full fixture observation inferred')
(E/'NCV_VALIDATION.json').write_text(json.dumps(out,indent=2)+'\n')
print(json.dumps({k:v for k,v in out.items() if k not in ['kani_classes','optimized_statement_features']},indent=2))
