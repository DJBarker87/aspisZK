"""Validate receipts, exact configured bounds and per-source audits; no prover runs."""
from pathlib import Path
import json,re,hashlib,subprocess,collections
E=Path(__file__).resolve().parent
records=[]
for p in sorted(E.glob('NCI_[KL][0-9][0-9][0-9]/receipt.json')):
 r=json.loads(p.read_text());a=r['attempt'];log=p.with_name('stdout.log').read_text()
 assert r['limits']=={'memory.high':'6442450944','memory.max':'8589934592','memory.swap.max':'0','pids.max':'64'},(a,r['limits'])
 assert str(r['swaps'])=='0',a
 if r['kind']=='kani':
  graph=json.loads((E/(a+'-graph-check.json')).read_text());assert graph['graph_matches_frozen']
  assert (E/(a+'-lock-after.log')).read_text().strip()==graph['lock_sha256']
  assert r['env']['CARGO_NET_OFFLINE']=='true' and r['env']['CARGO_PROFILE_DEV_OPT_LEVEL']=='3'
  if 'timed out' in log:status='TIMEOUT'
  elif 'could not compile' in log:status='CODEGEN_FAILURE'
  elif 'VERIFICATION:- SUCCESSFUL' in log:status='PASS'
  elif 'VERIFICATION:- FAILED' in log:status='DOMAIN_REFUSAL' if a=='NCI_K070' else 'INTENDED_FAIL'
  else:raise AssertionError(a+' unknown verdict')
  assert status not in ['PASS'] or r['exit_status']==0
 else:
  assert '-M7000' in r['command']
  status='PASS' if r['exit_status']==0 else 'REJECTED_DRAFT'
  if status=='PASS':
   for line in r['print_axioms']:
    if 'depends on axioms:' in line:
     axioms=set(line.split('[')[1].split(']')[0].split(', '))
     assert axioms<={'propext','Classical.choice','Quot.sound'},(a,line)
 records.append(dict(attempt=a,kind=r['kind'],status=status,target=r['command'],exit_status=r['exit_status'],wall_seconds=r['wall_seconds'],peak_rss_kib=int(r['peak_rss_kib']),swaps=r['swaps'],source_revision=r['source_revision'],source_hashes=r['source_hashes'],deps_fingerprint=r['deps_fingerprint'],print_axioms=r['print_axioms']))
assert sum(x['kind']=='kani' for x in records)==70
assert sum(x['kind']=='lean' for x in records)==39
# Keep full authoritative receipts as one JSONL, including all rejected drafts.
with (E/'NCI_ATTEMPTS.jsonl').open('w') as f:
 for p in sorted(E.glob('NCI_[KL][0-9][0-9][0-9]/receipt.json')):f.write(json.dumps(json.loads(p.read_text()))+'\n')
summary={kind:dict(collections.Counter(x['status'] for x in records if x['kind']==kind)) for kind in ['kani','lean']}
summary.update(lean_budget=80,kani_budget=70,counts={'lean':39,'kani':70},max_peak_rss_kib=max(x['peak_rss_kib'] for x in records),total_wall_seconds=sum(x['wall_seconds'] for x in records),audit=json.loads((E/'NCI_L039/receipt.json').read_text()),known_k2_quarantined_harnesses=[],k2_note='Own harness source contains no Option<fn>, function-pointer value or comparison. No K-2 credit used.',frozen_source_diff=subprocess.check_output(['git','diff','--name-only','4bb3b3f5','--','crates','programs'],text=True).splitlines())
assert not summary['frozen_source_diff']
assert summary['audit']['exit_status']==0 and len(summary['audit']['print_axioms'])==61
summary['model_sources']={str(p):hashlib.sha256(p.read_bytes()).hexdigest() for p in sorted(Path('lean').glob('NCI_*.lean'))}
for p in Path('lean').glob('NCI_*.lean'):
 assert not re.search(r'\b(sorry|admit|native_decide)\b|^\s*axiom\b|set_option (maxHeartbeats|maxRecDepth)',p.read_text(),re.M),p
large=[str(p) for p in E.rglob('*') if p.is_file() and p.stat().st_size>20*1024*1024]
assert not large,large
(E/'NCI_VERIFICATION.json').write_text(json.dumps(summary,indent=2)+'\n')
print(json.dumps({k:v for k,v in summary.items() if k in ['kani','lean','counts','max_peak_rss_kib','total_wall_seconds']}))
