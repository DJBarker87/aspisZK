"""Additive NHB-style receipt validation. Local gates never promote the driver."""
from pathlib import Path
import json,hashlib,re,subprocess,lzma
E=Path(__file__).resolve().parent;ROOT=E.parent.parent
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
limits={'memory.high':'6442450944','memory.max':'8589934592','memory.swap.max':'0','pids.max':'64'}
kmx='bcdf749b78eb6143789500d98d64ec3d407b8a17a6d1290c70c822473e8e9a67'
assert sha(E.parent/'kani-mitig-20261028/KMX_copy_stubs.patch')==kmx
assert all(sha(ROOT/p)==h for p,h in json.loads((E/'NHK_REUSE.json').read_text()).items())
results=[]
for p in sorted(E.glob('NHK_[KL][0-9][0-9][0-9]/receipt.json')):
 r=json.loads(p.read_text());a=r['attempt'];raw=(p.parent/'stdout.log').read_text()
 assert r['limits']==limits and str(r['swaps'])=='0',a
 ad=json.loads((E/(a+'-admission.json')).read_text());assert ad['exit']==0 and ad['reservation']['allowed'] is True,a
 for source,h in r['source_hashes'].items():assert sha(p.parent/'sources'/source)==h,(a,source)
 if r['kind']=='kani':
  graph=json.loads((E/(a+'-graph-check.json')).read_text());lock=json.loads((E/(a+'-lock-check.json')).read_text())
  assert graph['graph_matches_frozen'] and lock['unchanged'] and lock['before']==lock['after'],a
  assert graph['selected_closure'] and all('features' in x for x in graph['selected_closure']),a
  assert r['env']['CARGO_NET_OFFLINE']=='true' and r['env']['CARGO_PROFILE_DEV_OPT_LEVEL']=='3',a
  src=p.parent/'sources/NHK_src/crates/aspis-core/src/NHK_harness.rs';s=src.read_text()
  assert '#[kani::stub(core::ptr::copy_nonoverlapping,crate::KMX_stubs::KMX_copy_nonoverlapping)]' in s,a
  assert not re.search(r'\bstatic\s+(mut\s+)?\w+\s*:',s),a
  assert 'Option<fn' not in s and 'stub_verified' not in s,a
  if 'timed out' in raw or 'CBMC failed' in raw or r['exit_status'] in [124,137]:verdict='TOOL_LIMIT'
  elif r['exit_status']==0 and 'VERIFICATION:- SUCCESSFUL' in raw:verdict='PASS'
  elif 'Failed Checks:' in raw and re.search(r'\*\* 1 of \d+ failed',raw) and 'unwinding assertion' not in raw:verdict='ASSERTION_FAILED'
  else:verdict='OTHER_FAILURE'
 else:
  verdict='PASS' if r['exit_status']==0 else 'EXCLUDED_FAILURE'
  if verdict=='PASS' and r['kind']=='lean':
   for line in r['print_axioms']:
    assert 'sorryAx' not in line,line
    if 'axioms: [' in line:
     assert set(x.strip() for x in line.split('axioms: [',1)[1].rstrip(']').split(','))<={'propext','Classical.choice','Quot.sound'},line
 results.append(dict(attempt=a,kind=r['kind'],target=r['module'],verdict=verdict,exit_status=r['exit_status'],wall_seconds=r['wall_seconds'],peak_rss_kib=r['peak_rss_kib'],swaps=r['swaps'],source_revision=r['source_revision'],receipt=str(p.relative_to(E)),receipt_sha256=sha(p),print_axioms=r['print_axioms']))
rd={r['attempt']:r for r in results}
for name in ['NHK_MEMBERSHIP_PROGRESS.json','NHK_SPLIT_PROGRESS.json','NHK_WINDOW_PROGRESS.json']:
 if not (E/name).exists():continue
 for row in json.loads((E/name).read_text()):
  if not row['status'].startswith('CHECKED'):continue
  pos,neg=row['positive'],row['control'];assert rd[pos]['verdict']=='PASS' and rd[neg]['verdict']=='ASSERTION_FAILED',(pos,neg)
  cfg=[json.loads((E/n/'receipt.json').read_text()) for n in [pos,neg]]
  assert cfg[0]['native_command']==cfg[1]['native_command'] and cfg[0]['source_hashes']==cfg[1]['source_hashes'],(pos,neg)
  assert cfg[0]['env']['RUSTFLAGS']+' --cfg NHK_invert'==cfg[1]['env']['RUSTFLAGS'],(pos,neg)
for p in E.rglob('*'):
 if p.is_file():assert p.stat().st_size<=20*1024*1024,str(p)
if (E/'NHK_LEDGER_DELTA.json').exists():
 d=json.loads((E/'NHK_LEDGER_DELTA.json').read_text());assert d.get('newly_closed',[])==[],'Physical producer not yet validated; no promotion authorized'
(E/'NHK_RESULTS.json').write_text(json.dumps(dict(runs=results,counts={k:sum(r['kind']==k for r in results) for k in ['kani','lean','link','audit']},root='TX1:168',composed_rows_added=0),indent=2)+'\n')
print(json.dumps(dict(status='PASS',receipts=len(results),physical_producer='OPEN',newly_closed=[])))
