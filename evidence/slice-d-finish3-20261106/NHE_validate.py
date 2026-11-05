"""Additive NHE evidence validation; never relaxes predecessor predicates."""
from pathlib import Path
import json,hashlib,lzma,re,subprocess
E=Path(__file__).resolve().parent
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
limits={'memory.high':'6442450944','memory.max':'8589934592','memory.swap.max':'0','pids.max':'64'}
receipts=[]
for p in sorted(E.glob('NHE_[KLE][0-9][0-9][0-9]/receipt.json')):
 r=json.loads(p.read_text());a=r['attempt'];receipts.append(r)
 assert r['limits']==limits and str(r['swaps'])=='0',(a,'limits/swap')
 ad=json.loads((E/(a+'-admission.json')).read_text());assert ad['exit']==0 and ad['reservation']['allowed']is True,(a,'admission')
 for k in ['module','command','source_revision','source_hashes','deps_fingerprint','exit_status','wall_seconds','peak_rss_kib','print_axioms']:assert k in r,(a,k)
 if r['kind']=='lean'and r['exit_status']==0:assert all('sorryAx'not in line for line in r['print_axioms']),a
 if r['kind']=='kani':
  g=json.loads((E/(a+'-graph-check.json')).read_text());lock=json.loads((E/(a+'-lock-check.json')).read_text());source=json.loads((E/(a+'-source-check.json')).read_text())
  assert not source['errors']and g['graph_matches_frozen']and not g['new_package_tuples']and not g['edge_errors']
  assert lock['unchanged']and lock['before']==lock['after']=='5782e6a32026fdd95d252d0db7ea20b16716e6deb4f5a397e744886bb6ba22ef'
  assert r['env']['CARGO_NET_OFFLINE']=='true'and '-Copt-level=3'in r['env']['RUSTFLAGS']
  assert r['native_command'][r['native_command'].index('--harness-timeout')+1]=='90s'
  assert '--locked'not in r['native_command']
  root=next(z for z in g['selected_closure']if z['name']=='aspis-r1-cost-probe')
  assert {'default','private-leaf-salts','optimized-terminal','program-build'}<=set(root['features'])
  snap=E/a/'SOURCE_INDEX.json'
  if snap.exists():
   for name,z in json.loads(snap.read_text()).items():
    data=lzma.decompress((E/z['payload']).read_bytes());assert len(data)==z['bytes']and hashlib.sha256(data).hexdigest()==r['source_hashes'][name]==z['sha256']
  else:
   for p in (E/a/'sources').rglob('*'):
    if p.is_file():assert sha(p)==r['source_hashes'][str(p.relative_to(E/a/'sources'))]
counts={k:sum(r['attempt'].startswith('NHE_'+prefix)for r in receipts)for k,prefix in [('kani','K'),('lean_audit','L'),('extraction','E')]}
assert counts['kani']<=100 and counts['lean_audit']<=80 and counts['extraction']<=2
for i in range(1,101,2):
 a=f'NHE_K{i:03d}';b=f'NHE_K{i+1:03d}';p=json.loads((E/a/'receipt.json').read_text());n=json.loads((E/b/'receipt.json').read_text())
 assert p['exit_status']==0 and n['exit_status']==1 and p['module']==n['module']
 assert p['source_hashes']==n['source_hashes'],(a,b,'no source change or rename')
 assert 'VERIFICATION:- SUCCESSFUL'in(E/a/'stdout.log').read_text()
 assert 'Failed Checks: assertion failed: good'in(E/b/'stdout.log').read_text()
 assert 'VERIFICATION:- FAILED'in(E/b/'stdout.log').read_text()
for p in E.glob('NHE_*.lean'):
 assert not re.search(r'\b(sorry|axiom|admit|native_decide)\b|set_option\s+(maxRecDepth|maxHeartbeats)',p.read_text()),p
for p in E.rglob('*'):
 if p.is_file():assert p.stat().st_size<=20*1024*1024,('oversize',str(p))
assert not list(E.rglob('__pycache__'))
closed=json.loads((E/'NHE_CLOSED.json').read_text());delta=json.loads((E/'NHE_LEDGER_DELTA.json').read_text())
assert set(delta['new_closed_rows'])=={r for c in closed['functions']for r in c['rows']}=={'TX2:119','TX2:116','TX2:114'}
assert delta['no_other_status_change']and delta['not_a_premise_retirement']
base_path=E.parent/'ledger9-20261105/NGZ_LEDGER.json.xz'
base=json.loads(lzma.decompress(base_path.read_bytes()));baseline={r['row']:r for r in base['rows']}
assert len(baseline)==599
for c in closed['functions']:
 for name in c['rows']:
  assert baseline[name]['function']==c['function']and baseline[name]['composed_status']=='OPEN'
assert baseline['TX2:115']['composed_status']=='OPEN'

for c in closed['functions']:
 assert c['inner_hypotheses_remaining']==[]
 for a in [c['combined_replay'],c['ax2'],c['scan']]:assert json.loads((E/a/'receipt.json').read_text())['exit_status']==0
 raw=[json.loads(l[11:])for l in(E/c['ax2']/'stdout.log').read_text().splitlines()if l.startswith('NEP_RESULT ')]
 assert c['lean_root']in{r['root']for r in raw}
 assert all(r['equal'] and set(r['walked_axioms'])<={'propext','Classical.choice','Quot.sound'}for r in raw)
final=json.loads((E/'NHE_AUDIT.json').read_text());assert final['status']=='PASS'
raw=[json.loads(l[11:])for l in(E/final['raw_ax2']/'stdout.log').read_text().splitlines()if l.startswith('NEP_RESULT ')]
assert len(raw)==final['roots']and all(r['equal'] and set(r['walked_axioms'])<={'propext','Classical.choice','Quot.sound'}for r in raw)
scan=[json.loads(l)for l in(E/'NHE_LOADED_scan.jsonl').read_text().splitlines()]
assert len(scan)==final['modules']and all(not r['dangling']and not r['duplicate_owners']and r['imports_match']for r in scan)
catalog={r['module']:r['imports']for l in(E/'NHE_EXPECTED_IMPORTS.jsonl').read_text().splitlines()for r in[json.loads(l)]}
assert all(list(dict.fromkeys(r['loader_imports']))==r['imports']==catalog.get(r['module'])for r in scan)
fixtures=[json.loads(l[11:])for l in(E/'NHE_L023/stdout.log').read_text().splitlines()if l.startswith('NEP_RESULT ')]
assert len(fixtures)==8
assert json.loads((E/'NHE_L023/NHE_ProofDriver_BINARY_PIN.json').read_text())==json.loads((E/final['raw_ax2']/'NHE_ProofDriver_BINARY_PIN.json').read_text())
assert subprocess.run(['git','diff','--quiet','4bb3b3f51e16b4525f1d10336e2b0bcbbd775387','HEAD','--','crates','programs']).returncode==0
result=dict(status='PASS',counts=counts,new_composed_rows=3,headline='NOT ESTABLISHED',native_scalar_pairs=50,scalar_factor_composed_status='OPEN',new_trust=False,full_release_replay=False,shipped_sources_unchanged=True,elf_rebuild_trigger=False)
(E/'NHE_VALIDATION.json').write_text(json.dumps(result,indent=2)+'\n');print(json.dumps(result))
