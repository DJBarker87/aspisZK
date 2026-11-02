"""Read-only receipt reconciliation; writes only this job's evidence summary."""
from pathlib import Path
import subprocess,json,hashlib,re
R=Path(__file__).resolve().parents[2];E=R/'evidence/pv-uc-20261029'
rows=[]
for p in sorted(E.glob('native*/receipt.json')):
 x=json.loads(p.read_text());assert x['limits']==dict(MemoryHigh='6G',MemoryMax='8G',MemorySwapMax=0,TasksMax=64)
 t=(p.parent/'time.log').read_text();assert f'Exit status: {x["exit"]}' in t
 s=(p.parent/'output.log').read_text();i=s.find('Imported:');tail=s[i:] if i>=0 else s
 error=re.search(r'(?:\[\x1b\[91mError\x1b\[39m\] |Uncaught exception:)([\s\S]{0,1000})',tail)
 rows.append(dict(id=p.parent.name,**{k:x[k] for k in ['exit','wall','peak_rss_kib','swap','source_revision','expected_phase']},command=x['target'][x['target'].index('-v')+3:] if '-v' in x['target'] else x['target'],error_excerpt=error.group(0) if error else None,receipt_sha256=hashlib.sha256(p.read_bytes()).hexdigest()))
pending=[];refused=[]
for d in sorted(E.glob('native751*')):
 if d.is_dir() and not (d/'receipt.json').exists():
  decisions=[json.loads(p.read_text()) for p in d.glob('admission-*.json')]
  if any(a.get('allowed') is False for a in decisions):
   refused.append(dict(id=d.name,status='REFUSED BEFORE WORK; ID retired, no resubmission'));continue
  if (d/'admission-before.json').is_file():
   ad=json.loads((d/'admission-before.json').read_text())
   if ad.get('allowed') is True:pending.append(dict(id=d.name,status='PENDING: reconcile host done status before any next scope; never resubmit'))
lean=[]
for p in sorted(E.glob('lean750*/receipt.json')):
 x=json.loads(p.read_text());lean.append(dict(id=p.parent.name,**x))
assert len(rows)+len(pending)<=50 and len(lean)<=40
all_ids=[int(d.name[6:]) for d in E.glob('native751*') if d.is_dir()]
used_lean=[int(d.name[4:]) for d in E.glob('lean750*') if d.is_dir()]
(E/'attempts.json').write_text(json.dumps(dict(native_scopes_spent=len(rows)+len(pending),native_scopes_completed=len(rows),native_scopes_remaining=50-len(rows)-len(pending),spent_native_ids=[r['id'] for r in rows]+[r['id'] for r in pending],pending_native=pending,refused_native=refused,next_native_id=max(all_ids)+1,lean_attempts_spent=len(lean),lean_attempts_remaining=40-len(lean),next_lean_id=max(used_lean)+1 if used_lean else 75000,kani=0,rows=rows,lean_rows=lean),indent=2)+'\n')
paths=['tools/r1-cost-probe/src/bin/devnet_spend.rs']
paths+=subprocess.check_output(['git','ls-tree','-r','--name-only','683e01efee','tools/r1-cost-probe/src/bin/devnet_spend'],cwd=R,text=True).splitlines()
h=[]
for path in paths:
 old=subprocess.check_output(['git','show','683e01efee:'+path],cwd=R)
 current=(R/path).read_bytes();assert old==current,path
 h.append(dict(path=path,sha256=hashlib.sha256(current).hexdigest(),byte_identical=True))
assert not subprocess.check_output(['git','diff','683e01efee','--','crates','programs'],cwd=R)
(E/'source-boundaries.json').write_text(json.dumps(dict(revision=subprocess.check_output(['git','rev-parse','HEAD'],cwd=R,text=True).strip(),unchanged_fixture_target=h,no_crates_or_programs_change=True,source_files={str(p.relative_to(R)):hashlib.sha256(p.read_bytes()).hexdigest() for p in (R/'tools/r1-cost-probe/src/bin/user_client').glob('*.rs')}),indent=2)+'\n')
for p in E.rglob('*'):
 if p.is_file():assert p.stat().st_size<=20*1024**2,p
print('receipt summary verified:',len(rows),'completed native;',len(pending),'pending;',len(lean),'Lean; no Kani')
