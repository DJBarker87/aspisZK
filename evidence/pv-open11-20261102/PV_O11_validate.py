from pathlib import Path
import subprocess,json,hashlib,re
D=Path(__file__).parent
sha=lambda b:hashlib.sha256(b).hexdigest()
pins=json.loads((D/'PV_O11_input-pins.json').read_text())
for path,x in pins.items():
 b=subprocess.check_output(['git','show',x['blob']]);assert sha(b)==x['sha256'],path
rows=json.loads((D/'PV_O11_triage.json').read_text());assert len(rows)==69 and len({r['id'] for r in rows})==69
assert sum(x['live_owner'] is not None for x in rows)==14
rec={p.parent.name:json.loads(p.read_text()) for p in (D/'receipts').glob('*/receipt.json')};assert set(rec)=={'90400','90401','90402','90403','90404','90405','90406','90407','90497','90498','N90500','N90501','N90502','N90503','N90504','N90505','N90506','N90507'}
for label,r in rec.items():
 assert r['admission_allowed'] is True and r['admission_exit']==0 and int(r['swaps'])==0
 assert int(r['peak_rss_kib'])>0 and r['wall_seconds']>0 and r['revision']
 assert all(v in r['command'] for v in ['MemoryHigh=6G','MemoryMax=8G','MemorySwapMax=0','TasksMax=64'])
 if label=='90400': p=D/'failed/PV_O11_KindView-90400.lean.txt'
 elif label in ['90401']:p=D/'lean/PV_O11_KindView.lean'
 elif label=='90402':p=D/'lean/PV_O11_NEP_WALKER.lean'
 elif label in ['90403','90497']:p=D/'lean/PV_O11_NEP_Driver.lean'
 elif label=='N90500':p=D/'PV_O11_kind_native.rs'
 elif label=='N90501':p=D/'extract/lib.rs'
 elif label=='N90502':p=D/'extract/PV_O11_ErrorKind.llbc'
 elif label=='90404':p=D/'lean/PVO11Borrowed/Types.lean'
 elif label=='90405':p=D/'lean/PVO11Borrowed/Funs.lean'
 elif label=='90406':p=D/'lean/PV_O11_BorrowedLaw.lean'
 elif label in ['90407','90498']:p=D/'lean/PV_O11_BorrowedAudit.lean'
 elif label=='N90503':p=D/'borrowed/lib.rs'
 elif label=='N90504':p=D/'borrowed/PV_O11_Borrowed.llbc'
 elif label=='N90505':p=D/'capacity/lib.rs'
 elif label=='N90506':p=D/'failed/PV_O11_abort_native-N90506.rs.txt'
 elif label=='N90507':p=D/'PV_O11_abort_native.rs'
 else:raise AssertionError(label)
 assert sha(p.read_bytes())==r['source_sha256'],label
 expected=1 if label in ['90400','N90506'] else 2 if label=='N90502' else 0
 assert r['exit']==expected,(label,r['exit'])
audit=(D/'receipts/90497/output.log').read_text();results=[json.loads(x) for x in re.findall(r'NEP_RESULT (.*)',audit)]
assert len(results)==3 and all(x['equal'] and x['walked_axioms']==['propext'] for x in results)
assert 'NEP_FAILURE' not in audit
for p in (D/'lean').glob('PV_O11_Kind*.lean'):
 assert not re.search(r'\b(sorry|admit|axiom|native_decide)\b',p.read_text())
assert json.loads((D/'PV_O11_decoder-migration.json').read_text())['ok']
assert all(p.stat().st_size<20_000_000 for p in D.rglob('*') if p.is_file())
assert not list(D.rglob('*.olean')) and not list(D.rglob('*.rlib'))
for name in ['Types','Funs']:
 assert (D/('borrowed-generated/'+name+'.lean')).read_bytes()==(D/('lean/PVO11Borrowed/'+name+'.lean')).read_bytes()
newaudit=(D/'receipts/90498/output.log').read_text();newresults=[json.loads(x) for x in re.findall(r'NEP_RESULT (.*)',newaudit)]
assert len(newresults)==2 and all(x['equal'] and x['walked_axioms']==[] for x in newresults) and 'NEP_FAILURE' not in newaudit
assert json.loads((D/'capacity/PV_O11_capacity.llbc').read_text())['has_errors']
assert json.loads((D/'receipts/N90505/semantic-status.json').read_text())['accepted'] is False
assert json.loads((D/'PV_O11_abort-oom-result.json').read_text())['ok']
failed_native=json.loads((D/'PV_O11_abort-native-result.json').read_text());assert not failed_native['ok']
assert all(x['ok'] for x in failed_native['results'] if x['mode']!='oom')
for file in ['PV_O11_next-rows.json','PV_O11_write-all.json']:
 assert json.loads((D/file).read_text())['ok']
for label in ['90404','90405','90406','90407','90498']:
 assert all(x['ok'] for x in json.loads((D/('receipts/'+label+'/external-check.json')).read_text()))
 assert len(json.loads((D/('receipts/'+label+'/effective-external-resolution.json')).read_text()))==5673
runners={sha(p.read_bytes()) for p in (D/'inputs/runners').glob('*') if p.is_file()}
for label in ['90404','90405','90406','90407','90498','N90503','N90504','N90505','N90506','N90507']:
 assert rec[label]['failed_source_guard_sha256'] in runners,label
for file in ['lean/PV_O11_BorrowedLaw.lean']:
 assert not re.search(r'\b(sorry|admit|axiom|native_decide)\b',(D/file).read_text())
inspected={}
for file,count in [('PV_O11_open-sync.json',38),('PV_O11_ranked-links.json',26)]:
 report=json.loads((D/file).read_text())
 assert report['ok'] and len(report['checks'])==count and all(report['checks'].values()),file
 assert report['restored']==report['premises_removed']==report['premises_added']==report['premises_weakened']==0
 for row,r in report['rows'].items():
  assert row not in inspected and r['status']=='OPEN' and r['exact_premise']
  assert report['attempts'][row]==dict(source_inspection_passes=1,lean=0,native=0)
  inspected[row]=r['rank']
 for path,h in report.get('inputs',report.get('local_inputs',{})).items():
  assert sha((D/path).read_bytes())==h,(file,path)
 for path,pin in report.get('pins',{}).items():
  b=subprocess.check_output(['git','show',pin['blob']])
  assert sha(b)==pin['sha256'] and (D/pin['snapshot']).read_bytes()==b
 assert all(x['equal'] and x['actual']==x['expected'] for x in report.get('adopted_source_identity',{}).values())
assert sorted(inspected.values())==list(range(6,15))
assert set(inspected)=={'V171','V175','V172','V268','V271','V239','V249','V269','V403'}
provenance=json.loads((D/'PV_O11_io-provenance.json').read_text())
assert provenance['exit']==0 and len(provenance['inputs'])==9
for path,pin in provenance['inputs'].items():
 assert pin['equal'] and sha((D/path).read_bytes())==pin['sha256']==pin['snapshot_sha256']
print(json.dumps(dict(ok=True,rows=69,excluded=14,restored=0,lean_invocations=10,native_invocations=8,kani=0,nep_roots=5,new_source_inspections=len(inspected),endpoint_premises_removed=0)))
