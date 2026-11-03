"""Read-only receipt/source audit. Axiom classifications are SUMMARY-BASED."""
from pathlib import Path
import json,hashlib,subprocess,re
E=Path('evidence/pv-evhB-20261103');sha=lambda b:hashlib.sha256(b).hexdigest()
receipts=[json.loads(p.read_text()) for p in sorted(E.glob('receipt-*.json'))]
normal=[r['attempt'] for r in receipts if r['attempt']<=91296]
assert normal==list(range(91200,91200+len(normal)))
accepted={};failures=[]
for r in receipts:
 a=r['attempt'];assert 91200<=a<=91299
 raw=subprocess.check_output(['git','show',r['source_revision']+':'+r['source_path']])
 assert sha(raw)==r['source_sha256']
 assert r['wall'] and r['peak_rss_kbytes'] and r['exit'] is not None and r['swaps']=='0'
 assert r['admission']['allowed'] is True
 assert '-M7000' not in r['command'] # runner takes the exact numeric memory argument
 assert r['command'][-1]=='7000'
 for cap in ['MemoryHigh=6G','MemoryMax=8G','MemorySwapMax=0','TasksMax=64']:assert cap in r['command']
 p=E/('prepare-'+r['target']+'.json')
 if sha(p.read_bytes())!=r['deps_fingerprint']:p=E/'prepare-history'/(r['deps_fingerprint']+'.json')
 assert sha(p.read_bytes())==r['deps_fingerprint']
 prep=json.loads(p.read_text())['result'];assert prep['source_sha256']==r['source_sha256']
 staged=subprocess.check_output(['git','show',prep['source_revision']+':'+r['source_path']])
 assert staged==raw
 out=(E/f'out-{a}.log').read_text()
 if r['accepted']:
  assert r['exit']=='0' and 'error:' not in out and 'sorryAx' not in out
  assert Path(r['source_path']).read_bytes()==raw,'accepted source changed'
  assert r['axioms'],'missing summary-based axioms'
  for group in re.findall(r'depends on axioms: \[([^]]*)\]',out,re.S):
   assert set(re.findall(r'[A-Za-z_.]+',group))<={'propext','Classical.choice','Quot.sound'}
  accepted[r['target']]=r
 else:failures.append(dict(attempt=a,target=r['target'],source_sha256=r['source_sha256']))
for p in Path('lean').glob('PV_EVHB_*.lean'):
 assert p.stem in accepted,('unaccepted current source',str(p))
 s=p.read_text();assert not re.search(r'\b(sorry|axiom|admit|native_decide)\b',s)
 assert not re.search(r'set_option (maxRecDepth|maxHeartbeats)',s)
 for name in re.findall(r'^theorem (\w+)',s,re.M):assert '#print axioms '+name in s,(p,name)
assert not list(E.rglob('*'))==[]
assert all(p.stat().st_size<=20*1024*1024 for p in E.rglob('*') if p.is_file())
assert len(receipts)<=97
result=dict(source_revision=subprocess.check_output(['git','rev-parse','HEAD'],text=True).strip(),
 attempts=len(receipts),accepted_attempts=sum(r['accepted'] for r in receipts),failed_attempts=len(failures),
 remaining_attempts=97-len(receipts),next_normal_id=91200+len(normal),accepted_modules=sorted(accepted),failures=failures,
 peak_rss_kbytes=max(int(r['peak_rss_kbytes']) for r in receipts),swaps=0,
 axiom_audit='SUMMARY-BASED (ax1-prime); accepted only; raw NEP/cohort-coherence audit NOT performed',
 rows_removed=[],trust_fields_added=[],native_runs=0,kani_runs=0)
(E/'summary.json').write_text(json.dumps(result,indent=2)+'\n')
print('PASS receipts, immutable accepted sources, caps, standard summary axioms;',len(receipts),'attempts;',len(accepted),'modules')
