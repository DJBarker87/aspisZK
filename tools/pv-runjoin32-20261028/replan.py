"""Topologically reschedule uncompiled sources after a permitted import-only fix."""
from pathlib import Path
import json,subprocess,re,hashlib,time,shlex
R=Path(__file__).resolve().parents[2];E=R/'evidence/pv-runjoin32-20261028';plan=json.loads((E/'build-plan.json').read_text());failed='R1Z.PV_RunJoin_WithdrawalIdentification16';pin=plan['modules'][failed];assert pin['authority']=='h5 own git-tracked HEAD'
(E/'build-plan-before-import-fix.json').write_bytes((E/'build-plan.json').read_bytes())
rev=subprocess.check_output(['git','rev-parse','HEAD'],text=True).strip();path=pin['path'];b=subprocess.check_output(['git','show',rev+':'+path]);assert b==(R/path).read_bytes();old_sha=pin['sha256'];pin.update(sha256=hashlib.sha256(b).hexdigest(),git_blob=subprocess.check_output(['git','rev-parse',rev+':'+path],text=True).strip(),imports=re.findall(r'^(?:public )?import\s+(\S+)',b.decode(),re.M),revision=rev)
accepted={v['module'] for p in E.glob('modules-*.json') for v in json.loads(p.read_text()) if v['accepted']};external={v['module'].replace('/','.') for v in json.loads((E/'external-authority.json').read_text())};seen=set();active=set();order=[]
def visit(m):
 if m in external or m in accepted or m in seen:return
 assert m in plan['modules'],m
 assert m not in active,('cycle',m)
 active.add(m)
 for d in plan['modules'][m]['imports']:visit(d)
 active.remove(m);seen.add(m);order.append(m)
for m in plan['order']:visit(m)
chunks=[];batch=[]
for m in order:
 if m==failed:
  if batch:chunks.append(batch);batch=[]
  chunks.append([m])
 else:
  batch.append(m)
  if len(batch)==40:chunks.append(batch);batch=[]
if batch:chunks.append(batch)
plan.update(order=order,chunks=chunks,already_compiled=sorted(accepted),replan_revision=rev,import_fix=dict(module=failed,old_source_sha256=old_sha,new_source_sha256=pin['sha256'],added_import='R1Z.PV_Src_RootHelper',retained_failure=51322,replacement_is_singleton=True),next_attempt=51323)
(E/'build-plan.json').write_text(json.dumps(plan,indent=2)+'\n')
# Compiler inputs themselves are unchanged; only per-module revision reporting is generalized.
worker=R/'tools/pv-runjoin32-20261028/chunk-host.py';s=worker.read_text().replace("source_revision=plan['source_revision']","source_revision=pin.get('revision',plan['source_revision'])");worker.write_text(s)
code=r'''import pathlib,json,sys,hashlib
x=json.load(sys.stdin);p=pathlib.Path(x['plan']['workspace']);q=p/'sources'/(x['module'].replace('.','/')+'.lean');h=hashlib.sha256(q.read_bytes()).hexdigest();assert h in [x['old_sha'],x['pin']['sha256']],h
assert not (p/'objects'/(x['module'].replace('.','/')+'.olean')).exists()
a=p/'source-history'/h;a.parent.mkdir(exist_ok=True);a.write_bytes(q.read_bytes());q.write_text(x['source']);assert hashlib.sha256(q.read_bytes()).hexdigest()==x['pin']['sha256']
(p/'build-plan.json').write_text(json.dumps(x['plan']));(p/'chunk-host.py').write_text(x['worker']);print(json.dumps(dict(staged=x['module'],source_sha256=x['pin']['sha256'],worker_sha256=hashlib.sha256((p/'chunk-host.py').read_bytes()).hexdigest(),remaining_modules=len(x['plan']['order']),chunks=len(x['plan']['chunks']))))
'''
payload=json.dumps(dict(plan=plan,module=failed,old_sha=old_sha,pin=pin,source=b.decode(),worker=s))
for k in range(11):
 r=subprocess.run(['ssh','dombarker@100.108.41.90','python3 -c '+shlex.quote(code)],input=payload,text=True,capture_output=True)
 (E/f'import-fix-transport-{k}.json').write_text(json.dumps(dict(exit=r.returncode,stdout=r.stdout,stderr=r.stderr),indent=2)+'\n')
 if r.returncode!=255:break
 if k==10:raise RuntimeError('ten transport retries exhausted')
 print('transport cooldown60s; no compiler submitted',flush=True);time.sleep(60)
assert r.returncode==0,r.stderr
print(r.stdout);print('isolated replacement position',next(i for i,c in enumerate(chunks) if c==[failed]))
