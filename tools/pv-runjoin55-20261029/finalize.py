"""Collect original logs, retained failure identities and precise final accounting."""
from pathlib import Path
import json,hashlib,subprocess,shlex,lzma,re
R=Path(__file__).resolve().parents[2];E=R/'evidence/pv-runjoin55-20261029'
sha=lambda b:hashlib.sha256(b).hexdigest()
receipts=[json.loads(p.read_text()) for p in sorted(E.glob('receipt-*.json'))]
assert len(receipts)==100 and [r['attempt'] for r in receipts]==list(range(67700,67800))
modules=[dict(attempt=int(p.stem.split('-')[1]),**r) for p in sorted(E.glob('modules-*.json')) for r in json.loads(p.read_text())]
assert len(modules)==100
failed=[]
for r in modules:
 if r['accepted']:
  assert all('sorryAx' not in x for x in r['axioms'])
  continue
 pin=r['source'];ref=r['source_revision']+':'+pin['path'];b=subprocess.check_output(['git','show',ref],cwd=R)
 assert sha(b)==r['source_sha256']
 failed.append(dict(attempt=r['attempt'],module=r['module'],source_sha256=sha(b),revision=r['source_revision'],path=pin['path'],git_blob=subprocess.check_output(['git','rev-parse',ref],cwd=R,text=True).strip(),retained=True))
(E/'retained-failed-sources.json').write_text(json.dumps(failed,indent=2)+'\n')
files=[dict(path=r[k+'_path'],sha256=r[k+'_sha256']) for r in modules for k in ['output','time']]
code='''import sys,json,pathlib,hashlib
x=json.load(sys.stdin);o=[]
for v in x:
 b=pathlib.Path(v['path']).read_bytes();h=hashlib.sha256(b).hexdigest();assert h==v['sha256'];o.append(dict(path=v['path'],sha256=h,text=b.decode()))
print(json.dumps(o))'''
p=subprocess.run(['ssh','dombarker@100.108.41.90','python3 -c '+shlex.quote(code)],input=json.dumps(files),capture_output=True,text=True);assert p.returncode==0,p.stderr
logs=json.loads(p.stdout);assert len(logs)==200
(E/'original-module-logs.json.xz').write_bytes(lzma.compress(json.dumps(logs).encode()))
(E/'original-module-log-manifest.json').write_text(json.dumps([dict(path=x['path'],sha256=x['sha256'],bytes=len(x['text'].encode())) for x in logs],indent=2)+'\n')
allowed={'propext','Classical.choice','Quot.sound'}
for r in modules:
 if not r['accepted']:continue
 for line in r['axioms']:
  m=re.search(r'axioms: \[([^]]*)\]',line)
  if m:assert set(m[1].replace(' ','').split(','))<=allowed,(r['module'],line)
# Audit every added theorem; after-audit run is an imported definition with its own accepted print at 67767.
design=json.loads((E/'audit-design.json').read_text());covered=set(n for d in design.values() for n in d['names']);missing=[]
plan=json.loads((E/'build-plan.json').read_text())
for r in modules:
 if not r['accepted'] or r['attempt']==67723 or r['attempt']>=67797:continue
 src=(R/plan['modules'][r['module']]['path']).read_text()
 for n in re.findall(r'^theorem\s+(\w+)',src,re.M):
  if r['module']+'.'+n not in covered:missing.append(r['module']+'.'+n)
assert not missing,missing
(E/'audit-coverage.json').write_text(json.dumps(dict(all_added_credited_theorems_covered=True,printed_names=len(covered),definition_audited_in_own_receipt={'R1Z.PV_RunJoin_NativeAfterAudit55.run':67767},excluded_uncredited_module='R1Z.PV_RunJoin_BackendStore55',audits=[r['attempt'] for r in receipts if r['attempt']>=67797]),indent=2)+'\n')
changed=subprocess.check_output(['git','diff','--name-only','fc300a706a..HEAD'],cwd=R,text=True).splitlines()
assert not any('/PV_RJDec_' in x or '/PV_OWN' in x for x in changed)
identity={}
for label,args in [('frozen_rust_client',['82566acdfb','--','crates','programs','tools/r1-cost-probe']),('fixed_links',['fc300a706a','--','docs/research/v8-r0-zk-20261009/lean/R1Z/PV_RunJoin_PublishSkeleton54.lean'])]:
 diff=subprocess.check_output(['git','diff',*args],cwd=R);assert not diff;identity[label]=dict(diff_empty=True,arguments=args)
identity.update(protected_prefixes_unchanged=True,step4_started=False,guard_sha256=sha((R/'tools/pv-runjoin55-20261029/compile.py').read_bytes()),source_revision=subprocess.check_output(['git','rev-parse','HEAD'],cwd=R,text=True).strip())
(E/'boundaries.json').write_text(json.dumps(identity,indent=2)+'\n')
summary=dict(attempts=100,accepted_attempts=sum(r['accepted'] for r in receipts),failed_attempts=sum(not r['accepted'] for r in receipts),excluded_accepted_attempts=[67723],credited_accepted_attempts=sum(r['accepted'] for r in receipts)-1,kani=0,peak_rss_bytes=max(r['peak_rss_bytes'] for r in receipts),swaps=sum(r['swaps'] for r in receipts),rows_removed=[],endpoint_premises=dict(removed=0,added=0,weakened=0,changed=0),discharged_links_this_round=[],retained_links=['CommonSample','BackendInput','FinishContext','QueryAppend','NodeAppend','PublishOrder'],audit_source_revision=receipts[-1]['source_revision'],audits=[{k:r[k] for k in ['attempt','modules','exit','host_wall_seconds','peak_rss_bytes','swaps','source_revision','accepted']} for r in receipts if r['attempt']>=67797],guard_sha256=identity['guard_sha256'],scope_overlap=dict(attempts=[67722,67723],credit_excluded=67723,replacement=67728))
(E/'SUMMARY.json').write_text(json.dumps(summary,indent=2)+'\n')
(E/'commits.txt').write_text(subprocess.check_output(['git','log','--oneline','fc300a706a..HEAD'],cwd=R,text=True))
print(json.dumps({k:summary[k] for k in ['attempts','accepted_attempts','failed_attempts','credited_accepted_attempts','peak_rss_bytes','swaps','audit_source_revision']}))
