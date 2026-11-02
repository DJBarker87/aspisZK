from pathlib import Path
import subprocess,json,hashlib,re
D=Path(__file__).parent
sha=lambda b:hashlib.sha256(b).hexdigest()
pins=json.loads((D/'PV_O11_input-pins.json').read_text())
for path,x in pins.items():
 b=subprocess.check_output(['git','show',x['blob']]);assert sha(b)==x['sha256'],path
rows=json.loads((D/'PV_O11_triage.json').read_text());assert len(rows)==69 and len({r['id'] for r in rows})==69
assert sum(x['live_owner'] is not None for x in rows)==14
rec={p.parent.name:json.loads(p.read_text()) for p in (D/'receipts').glob('*/receipt.json')};assert set(rec)=={'90400','90401','90402','90403','90497','N90500','N90501','N90502'}
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
 else:p=D/'extract/PV_O11_ErrorKind.llbc'
 assert sha(p.read_bytes())==r['source_sha256'],label
 expected=1 if label=='90400' else 2 if label=='N90502' else 0
 assert r['exit']==expected,(label,r['exit'])
audit=(D/'receipts/90497/output.log').read_text();results=[json.loads(x) for x in re.findall(r'NEP_RESULT (.*)',audit)]
assert len(results)==3 and all(x['equal'] and x['walked_axioms']==['propext'] for x in results)
assert 'NEP_FAILURE' not in audit
for p in (D/'lean').glob('PV_O11_Kind*.lean'):
 assert not re.search(r'\b(sorry|admit|axiom|native_decide)\b',p.read_text())
assert json.loads((D/'PV_O11_decoder-migration.json').read_text())['ok']
assert all(p.stat().st_size<20_000_000 for p in D.rglob('*') if p.is_file())
assert not list(D.rglob('*.olean')) and not list(D.rglob('*.rlib'))
print(json.dumps(dict(ok=True,rows=69,excluded=14,restored=0,lean_invocations=5,native_invocations=3,kani=0,nep_roots=3,endpoint_premises_removed=0)))
