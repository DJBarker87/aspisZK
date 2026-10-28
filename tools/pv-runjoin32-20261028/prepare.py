"""Prepare fresh private replay inputs; no Lean launched and no old object written."""
from pathlib import Path
import json,hashlib,subprocess,shlex
R=Path(__file__).resolve().parents[2];E=R/'evidence/pv-runjoin32-20261028'
H='/home/dombarker/project-offloads/codex-pv-runjoin-20261026';P=H+'/runjoin32-lean'
x=json.loads((E/'focused-resolution.json').read_text());src=json.loads((E/'focused-project-sources.json').read_text());assert not x['unpinned']
seen=set();order=[];active=set()
def visit(m):
 if m not in src or m in seen:return
 assert m not in active,m
 active.add(m)
 for d in x['resolved'][m]['imports']:visit(d)
 active.remove(m);seen.add(m);order.append(m)
for m in src:visit(m)
# Endpoint audit itself is reserved for one audit after dependency replay.
order.remove('R1Z.PV_RunJoin_EndpointAudit20')
plan=dict(source_revision=x['head'],research_revision=x['research_revision'],workspace=P,roots=['R1Z.PV_RunJoin_EndpointAudit20','R1Z.PV_RunJoin_LaneDenotation31','R1Z.PV_RunJoin_NativeSnapshot31','R1Z.PV_RunJoin_FinalAudit31'],order=order,chunks=[order[i:i+40] for i in range(0,len(order),40)],modules={m:x['resolved'][m] for m in src},caps=dict(MemoryHigh='6G',MemoryMax='8G',MemorySwapMax=0,TasksMax=64,Lean_M=7000),old_cache_retained=H+'/runjoin24-lean')
(E/'build-plan.json').write_text(json.dumps(plan,indent=2)+'\n')
external=json.loads(subprocess.check_output(['git','show',x['research_revision']+':evidence/pv-replay-20261027/receipts/external-object-manifest.json']))
(E/'external-authority.json').write_text(json.dumps(external,indent=2)+'\n')
code=r'''import pathlib,json,hashlib,sys
x=json.load(sys.stdin);p=pathlib.Path(x['workspace']);assert not p.exists(),'fresh workspace already exists'
p.mkdir();(p/'objects').mkdir();(p/'sources').mkdir();(p/'external').mkdir();(p/'evidence').mkdir()
checks=[]
for v in x['external']:
 m=v['module'].replace('/','.');q=pathlib.Path(v['path']);sha=hashlib.sha256(q.read_bytes()).hexdigest() if q.is_file() else None
 checks.append(dict(module=m,path=str(q),sha256=sha,expected=v['object_sha256'],match=sha==v['object_sha256']))
 if sha!=v['object_sha256']:continue
 dest=p/'external'/(m.replace('.','/')+'.olean');dest.parent.mkdir(parents=True,exist_ok=True);dest.symlink_to(q)
 # Companions belong to the same pinned external object location; retain hashes.
 for suffix in ['.olean.private','.olean.server','.ilean','.so']:
  c=q.with_suffix(suffix)
  if c.is_file():
   d=dest.with_suffix(suffix);d.symlink_to(c)
   checks[-1].setdefault('companions',[]).append(dict(path=str(c),sha256=hashlib.sha256(c.read_bytes()).hexdigest()))
(p/'evidence/external-check.json').write_text(json.dumps(checks,indent=2))
assert all(v['match'] for v in checks),[v for v in checks if not v['match']]
for m,s in x['sources'].items():
 q=p/'sources'/(m.replace('.','/')+'.lean');q.parent.mkdir(parents=True,exist_ok=True);q.write_text(s)
 assert hashlib.sha256(q.read_bytes()).hexdigest()==x['plan']['modules'][m]['sha256'],m
base=json.load(open('/home/dombarker/project-offloads/r1-privacy-build-integration-20261019/env/J.json'))
env=base.copy();env['LEAN_PATH']=str(p/'objects')+':'+str(p/'external');(p/'J.json').write_text(json.dumps(env));(p/'build-plan.json').write_text(json.dumps(x['plan']))
print(json.dumps(dict(external_count=len(checks),external_all_match=all(v['match'] for v in checks),project_count=len(x['sources']),lean_path=env['LEAN_PATH'],toolchain={k:v for k,v in base.items() if k!='LEAN_PATH'},fresh=True,old_workspace_written=False)))
'''
r=subprocess.run(['ssh','dombarker@100.108.41.90','python3 -c '+shlex.quote(code)],input=json.dumps(dict(workspace=P,external=external,sources=src,plan=plan)),text=True,capture_output=True)
(E/'prepare-transport.json').write_text(json.dumps(dict(exit=r.returncode,stdout=r.stdout,stderr=r.stderr),indent=2)+'\n')
assert r.returncode==0,r.stderr
(E/'prepare.json').write_text(r.stdout)
subprocess.run(['scp','-q','dombarker@100.108.41.90:'+P+'/evidence/external-check.json',str(E/'external-hash-check.json')],check=True)
print(r.stdout);print('chunks',len(plan['chunks']),'modules',len(order))
