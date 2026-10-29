"""Collect original logs, retained failure identities and precise final accounting."""
from pathlib import Path
import json,hashlib,subprocess,shlex,lzma,re
R=Path(__file__).resolve().parents[2];E=R/'evidence/pv-runjoin57-20261029'
sha=lambda b:hashlib.sha256(b).hexdigest()
receipts=[json.loads(p.read_text()) for p in sorted(E.glob('receipt-*.json'))]
assert [r['attempt'] for r in receipts]==list(range(68500,68511))+list(range(68597,68600))
modules=[dict(attempt=int(p.stem.split('-')[1]),**r) for p in sorted(E.glob('modules-*.json')) for r in json.loads(p.read_text())]
assert len(modules)==len(receipts)
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
logs=json.loads(p.stdout);assert len(logs)==2*len(receipts)
(E/'original-module-logs.json.xz').write_bytes(lzma.compress(json.dumps(logs).encode()))
(E/'original-module-log-manifest.json').write_text(json.dumps([dict(path=x['path'],sha256=x['sha256'],bytes=len(x['text'].encode())) for x in logs],indent=2)+'\n')
allowed={'propext','Classical.choice','Quot.sound'}
for r in modules:
 if not r['accepted']:continue
 for line in r['axioms']:
  m=re.search(r'axioms: \[([^]]*)\]',line)
  if m:assert set(filter(None,re.sub(r'\s+','',m[1]).split(',')))<=allowed,(r['module'],line)
# Audit every added theorem against the three focused audit roots.
design=json.loads((E/'audit-design.json').read_text());covered=set(n for d in design.values() for n in d['names']);missing=[]
plan=json.loads((E/'build-plan.json').read_text())
for r in modules:
 if not r['accepted']  or r['attempt']>=68597:continue
 src=(R/plan['modules'][r['module']]['path']).read_text()
 for n in re.findall(r'^theorem\s+(\w+)',src,re.M):
  if r['module']+'.'+n not in covered:missing.append(r['module']+'.'+n)
assert not missing,missing
(E/'audit-coverage.json').write_text(json.dumps(dict(all_added_credited_theorems_covered=True,printed_names=len(covered),audits=[r['attempt'] for r in receipts if r['attempt']>=68597]),indent=2)+'\n')
changed=subprocess.check_output(['git','diff','--name-only','9a2672562d..HEAD'],cwd=R,text=True).splitlines()
assert not any('/PV_RJDec_' in x or '/PV_OWN' in x for x in changed)
identity={}
for label,args in [('frozen_rust_client',['82566acdfb','--','crates','programs','tools/r1-cost-probe']),('fixed_links',['9a2672562d','--','docs/research/v8-r0-zk-20261009/lean/R1Z/PV_RunJoin_PublishSkeleton54.lean'])]:
 diff=subprocess.check_output(['git','diff',*args],cwd=R);assert not diff;identity[label]=dict(diff_empty=True,arguments=args)
identity.update(protected_prefixes_unchanged=True,step4_started=False,guard_sha256=sha((R/'tools/pv-runjoin57-20261029/compile.py').read_bytes()),source_revision=subprocess.check_output(['git','rev-parse','HEAD'],cwd=R,text=True).strip())
(E/'boundaries.json').write_text(json.dumps(identity,indent=2)+'\n')
summary=dict(skeleton_decomposition_credit=False,all_link_witness_proved=False,context_candidate_unverified=True,release_credit=False,attempts=len(receipts),accepted_attempts=sum(r['accepted'] for r in receipts),failed_attempts=sum(not r['accepted'] for r in receipts),excluded_accepted_attempts=[],credited_accepted_attempts=sum(r['accepted'] for r in receipts),kani=0,peak_rss_bytes=max(r['peak_rss_bytes'] for r in receipts),swaps=sum(r['swaps'] for r in receipts),rows_removed=[],endpoint_premises=dict(removed=0,added=0,weakened=0,changed=0),discharged_links_this_round=[],retained_links=['CommonSample','BackendInput','FinishContext','QueryRange','QueryContext','QueryAppend','NodeAppend','PublishOrder'],audit_source_revision=receipts[-1]['source_revision'],audits=[{k:r[k] for k in ['attempt','modules','exit','host_wall_seconds','peak_rss_bytes','swaps','source_revision','accepted']} for r in receipts if r['attempt']>=68597],guard_sha256=identity['guard_sha256'],scope_overlap=dict(attempts=[],all_sequential=True),unused_attempt_ids=list(range(68511,68597)),stop_reason='Checked in-range missing-word source/link obstruction: range-only full conjunction contradicts any successful run at a representable opening offset. Further provenance correction compiled as candidate; its all-link witness remains unproved; no link-discharge stage started.')
(E/'SUMMARY.json').write_text(json.dumps(summary,indent=2)+'\n')
(E/'commits.txt').write_text(subprocess.check_output(['git','log','--oneline','9a2672562d..HEAD'],cwd=R,text=True))
print(json.dumps({k:summary[k] for k in ['attempts','accepted_attempts','failed_attempts','credited_accepted_attempts','peak_rss_bytes','swaps','audit_source_revision']}))
