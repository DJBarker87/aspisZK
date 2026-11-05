from pathlib import Path
import json,hashlib,re,sys,lzma
E=Path(__file__).resolve().parent
limits={'memory.high':'6442450944','memory.max':'8589934592','memory.swap.max':'0','pids.max':'64'}
checks=[];receipts=[]
for p in sorted(E.glob('NGW_[KLE][0-9][0-9][0-9]/receipt.json')):
 x=json.loads(p.read_text());a=x['attempt'];receipts.append(x)
 assert x['limits']==limits,(a,'caps');assert str(x['swaps'])=='0',(a,'swap')
 for k in ['module','command','source_revision','source_hashes','deps_fingerprint','exit_status','wall_seconds','peak_rss_kib','print_axioms']:assert k in x,(a,k)
 ad=json.loads((E/(a+'-admission.json')).read_text());assert ad['exit']==0 and ad['reservation']['allowed'] is True,(a,'admission')
 if x['kind']=='kani':
  sourcecheck=json.loads((E/(a+'-source-check.json')).read_text())
  if sourcecheck['errors']:
   assert a in ['NGW_K031','NGW_K032'] and x['exit_status']!=0
   assert 'Checking harness' not in (E/a/'stdout.log').read_text()
   checks.append(dict(attempt=a,outcome='EXCLUDED strict source preflight rejection; no Kani run'))
   continue
  graph=json.loads((E/(a+'-graph-check.json')).read_text());lock=json.loads((E/(a+'-lock-check.json')).read_text());assert graph['graph_matches_frozen'] and lock['unchanged'],(a,'lock')
  assert x['env']['CARGO_NET_OFFLINE']=='true';assert '-Copt-level=3' in x['env']['RUSTFLAGS'];assert x['native_command'][x['native_command'].index('--harness-timeout')+1]=='90s'
  # Controls are expected failures; preserve all other failures without credit.
  checks.append(dict(attempt=a,outcome='pass' if x['exit_status']==0 else 'expected-control-or-excluded',features=len(graph['selected_closure'])))
 elif x['kind']=='lean' and x['exit_status']==0:
  assert not any('sorryAx' in s for s in x['print_axioms']),a
for p in E.rglob('*'):
 if p.is_file():assert p.stat().st_size<=20*1024*1024,('oversize',str(p))
for p in E.glob('NGW*.lean'):
 s=p.read_text();assert not re.search(r'\b(sorry|axiom|admit|native_decide)\b|set_option\s+(maxRecDepth|maxHeartbeats)',s),str(p)
assert not list(E.rglob('__pycache__'))
# Every closed row requires explicit complete evidence, never an accepted child premise.
p=E/'NGW_CLOSED.json'
if p.exists():
 for row in json.loads(p.read_text())['functions']:
  assert row['inner_hypotheses_remaining']==[],row['function']
  for positive,negative in row['native_pairs']:
   for a,rc in [(positive,0),(negative,1)]:
    x=json.loads((E/a/'receipt.json').read_text());assert x['exit_status']==rc
    log=(E/a/'stdout.log').read_text();assert ('VERIFICATION:- SUCCESSFUL' if rc==0 else 'VERIFICATION:- FAILED') in log
    assert not re.search(r'timed out|memory limit exceeded|SIGKILL',log,re.I)
  assert row['lean_root'];assert row['combined_replay'];assert row['ax2'];assert row['scan']
# Additive ledger check: inherited status/source rows remain immutable.
base=json.loads(lzma.decompress((E.parent/'ledger8-20261105/NGJ_LEDGER.json.xz').read_bytes()))
rows={r['row']:r for r in base['rows']}
delta=json.loads((E/'NGW_LEDGER_DELTA.json').read_text())
assert delta['no_other_status_change'] and delta['not_a_premise_retirement']
closed=json.loads((E/'NGW_CLOSED.json').read_text())
assert set(delta['new_closed_rows'])=={r for c in closed['functions'] for r in c['rows']}
for c in closed['functions']:
 for row in c['rows']:assert rows[row]['function']==c['function'] and rows[row]['composed_status']=='OPEN'
 for a in [c['combined_replay'],c['ax2'],c['fixtures'],c['scan']]:assert json.loads((E/a/'receipt.json').read_text())['exit_status']==0
 raw=[json.loads(l[11:])for l in(E/c['ax2']/'stdout.log').read_text().splitlines()if l.startswith('NEP_RESULT ')]
 assert c['lean_root'] in {r['root']for r in raw}
 assert all(set(r['walked_axioms'])<={'propext','Classical.choice','Quot.sound'}for r in raw)
 scans=[json.loads(l)for l in(E/'NGW_LOADED_scan.jsonl').read_text().splitlines()]
 assert all(not r['dangling'] and not r['duplicate_owners'] and r['imports_match']for r in scans)
 assert len([l for l in(E/c['fixtures']/'stdout.log').read_text().splitlines()if l.startswith('NEP_RESULT ')])==8
for positive,negative in [pair for c in closed['functions'] for pair in c['native_pairs']]:
 x=json.loads((E/positive/'receipt.json').read_text());y=json.loads((E/negative/'receipt.json').read_text())
 assert x['module']==y['module'] and x['source_hashes']==y['source_hashes']
 for a in [positive,negative]:assert not json.loads((E/(a+'-source-check.json')).read_text())['errors']
summary=dict(validation='PASS',receipts=len(receipts),counts={kind:sum(x['attempt'].startswith(prefix) for x in receipts) for kind,prefix in [('kani','NGW_K'),('lean_audit','NGW_L'),('extraction','NGW_E')]},kani=checks,trust='unchanged P6/D188 option A and accepted runtime rows; no headline premise removal')
(E/'NGW_VALIDATION.json').write_text(json.dumps(summary,indent=2)+'\n');print(json.dumps({k:v for k,v in summary.items() if k!='kani'}))
