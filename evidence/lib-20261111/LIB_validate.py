"""Validate own source receipts and raw ax2 evidence without changing verdicts."""
from pathlib import Path
import json,hashlib,lzma,subprocess
E=Path(__file__).resolve().parent
standard={'propext','Classical.choice','Quot.sound'}
sha=lambda b:hashlib.sha256(b).hexdigest()
groups=json.loads((E/'LIB_AUDIT_ROOTS.json').read_text())['groups'];allrows=[];audits=[]
for i,group in enumerate(groups):
 p=E/'LIB_audit'/f'proof{i}'/f'proof{i}.json';a=json.loads(p.read_text());rs=a['results']
 assert sorted(r['root'] for r in rs)==sorted(group)
 assert all(set(r['walked_axioms'])<=standard and set(r['collect_axioms'])<=standard for r in rs)
 assert all(r['equal']==(set(r['walked_axioms'])==set(r['collect_axioms'])) for r in rs)
 mismatches=[r for r in rs if not r['equal']]
 assert a['exit_status']==(1 if mismatches else 0)
 if mismatches:assert p.with_suffix('.log').read_text().count('raw graph disagrees with collectAxioms')==len(mismatches)
 audits.append(dict(target=a['target'],exit_status=a['exit_status'],validated=a['validated'],mismatches=mismatches));allrows+=rs
assert len({r['root']for r in allrows})==len(allrows)
summary=dict(roots=len(allrows),raw_standard_only=True,audits=audits,strict_failures_retained=True,disposition="Raw axiom sets pass under C3-BIN (ab')(3); collector discrepancies remain tooling findings")
(E/'LIB_FINAL_AUDIT_SUMMARY.json').write_text(json.dumps(summary,indent=2)+'\n')
for r in json.loads((E/'LIB_FINAL_SOURCE_PINS.json').read_text()):
 assert sha(Path(r['source']).read_bytes())==r['sha256']
 receipt=json.loads(Path(r['receipt']).read_text());assert receipt['exit_status']==0
 assert r['sha256'] in receipt['source_hashes'].values()
 assert all('sorryAx' not in a for a in receipt['print_axioms'])
receipts=[]
for p in sorted(E.glob('LIB_L[0-9][0-9][0-9]/receipt.json')):
 r=json.loads(p.read_text());n=int(r['attempt'][-3:])
 if n<93:continue
 assert r['limits']=={'memory.high':'6442450944','memory.max':'8589934592','memory.swap.max':'0','pids.max':'64'}
 a=json.loads((E/(r['attempt']+'-admission.json')).read_text());assert a['exit']==0 and a['reservation']['allowed'] is True
 disks=list(E.glob(r['attempt']+'-disk-*.json'));assert disks and all(json.loads(q.read_text())['free']>=40*1024**3 for q in disks)
 assert all(k in r for k in ['wall_seconds','peak_rss_kib','swaps','source_revision','print_axioms'])
 receipts.append({k:r[k]for k in ['attempt','module','exit_status','wall_seconds','peak_rss_kib','swaps','source_revision']})
assert len(receipts)<=250
for p in E.glob('*.xz'):
 q=p.with_suffix('.sha256')
 if q.exists():assert sha(lzma.decompress(p.read_bytes()))==q.read_text().split()[0],p
assert not [str(p)for p in E.rglob('*')if p.is_file() and p.stat().st_size>20_000_000]
subprocess.run(['git','diff','--exit-code','4bb3b3f51e16b4525f1d10336e2b0bcbbd775387','--','crates','programs/r1-cost-probe','Cargo.lock'],check=True,stdout=subprocess.DEVNULL)
subprocess.run(['git','diff','--exit-code','b936275465','--','programs/aspis-pool'],check=True,stdout=subprocess.DEVNULL)
subprocess.run(['git','diff','--check'],check=True)
(E/'LIB_FINAL_VALIDATION.json').write_text(json.dumps(dict(validated=True,resumed_scopes=len(receipts),budget=250,kani=0,extraction=0,raw_roots=len(allrows),scopes=receipts,frozen_source_unchanged=True,headline_established=False,ledger_credit_claimed=False),indent=2)+'\n')
print(json.dumps(dict(validated=True,resumed_scopes=len(receipts),roots=len(allrows))))
