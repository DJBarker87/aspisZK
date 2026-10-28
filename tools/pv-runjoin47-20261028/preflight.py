"""Read-only source/object/external/fingerprint preflight for the fresh closure."""
from pathlib import Path
import subprocess,json,shlex,hashlib,sys,time
R=Path(__file__).resolve().parents[2];E=R/'evidence/pv-runjoin47-20261028';plan=json.loads((E/'build-plan.json').read_text());accepted={v['module']:v for p in list((R/'evidence/pv-runjoin32-20261028').glob('modules-*.json'))+list((R/'evidence/pv-runjoin33-20261028').glob('modules-*.json'))+list((R/'evidence/pv-runjoin34-20261028').glob('modules-*.json'))+list((R/'evidence/pv-runjoin35-20261028').glob('modules-*.json'))+list((R/'evidence/pv-runjoin38-20261028').glob('modules-*.json'))+list((R/'evidence/pv-runjoin39-20261028').glob('modules-*.json'))+list((R/'evidence/pv-runjoin40-20261028').glob('modules-*.json'))+list((R/'evidence/pv-runjoin41-20261028').glob('modules-*.json'))+list((R/'evidence/pv-runjoin43-20261028').glob('modules-*.json'))+list((R/'evidence/pv-runjoin44-20261028').glob('modules-*.json'))+list((R/'evidence/pv-runjoin45-20261028').glob('modules-*.json'))+list((R/'evidence/pv-runjoin46-20261028').glob('modules-*.json'))+list(E.glob('modules-*.json')) for v in json.loads(p.read_text()) if v['accepted']};excluded=set(sys.argv[1:]) if len(sys.argv)>1 else {'R1Z.PV_RunJoin_EndpointAudit20'}
assert set(plan['modules'])-set(accepted)<=excluded,sorted(set(plan['modules'])-set(accepted)-excluded)
# h5 current-HEAD agreement: source-identical earlier revisions retain provenance.
batch=subprocess.Popen(['git','cat-file','--batch'],stdin=subprocess.PIPE,stdout=subprocess.PIPE)
checks=[]
for m,v in plan['modules'].items():
 if not v['authority'].startswith('h5'):continue
 batch.stdin.write(('HEAD:'+v['path']+'\n').encode());batch.stdin.flush();line=batch.stdout.readline().decode().split();assert len(line)>=3,(m,line);b=batch.stdout.read(int(line[-1]));assert batch.stdout.read(1)==b'\n';h=hashlib.sha256(b).hexdigest();checks.append(dict(module=m,path=v['path'],HEAD_blob=line[0],expected=v['sha256'],actual=h,match=h==v['sha256']))
batch.stdin.close();batch.wait();assert all(x['match'] for x in checks)
(E/'current-head-source-check.json').write_text(json.dumps(checks,indent=2)+'\n')
external=json.loads((E/'external-authority.json').read_text());irs=json.loads((E/'external-ir-companions.json').read_text())
code=r'''import pathlib,json,hashlib,sys
x=json.load(sys.stdin);p=pathlib.Path(x['workspace']);sha=lambda q:hashlib.sha256(q.read_bytes()).hexdigest();projects=[];externals=[];deps=[];ir=[]
for m,v in x['accepted'].items():
 rel=m.replace('.','/');s=p/'sources'/(rel+'.lean');o=p/'objects'/(rel+'.olean');projects.append(dict(module=m,source_sha256=sha(s),expected_source_sha256=x['pins'][m]['sha256'],object_sha256=sha(o),expected_object_sha256=v['object_sha256']))
 for d,r in v['dependencies'].items():
  dr=d.replace('.','/')+'.olean';q=next((root/dr for root in [p/'objects',p/'external'] if (root/dr).is_file()),None);h=sha(q) if q else None;deps.append(dict(module=m,dependency=d,path=str(q),sha256=h,expected=r['sha256'],match=h==r['sha256']))
for v in x['external']:
 m=v['module'].replace('/','.');q=p/'external'/(m.replace('.','/')+'.olean');h=sha(q) if q.is_file() else None;externals.append(dict(module=m,path=str(q),sha256=h,expected=v['object_sha256'],match=h==v['object_sha256']))
for v in x['ir']:
 q=p/'external'/(v['module'].replace('.','/')+'.ir');h=sha(q) if q.is_file() else None;ir.append(dict(module=v['module'],sha256=h,expected=v['sha256'],match=h==v['sha256']))
env=json.load(open(p/'J.json'));base=json.load(open('/home/dombarker/project-offloads/r1-privacy-build-integration-20261019/env/J.json'));toolchain={k:env[k]==base.get(k) for k in env if k!='LEAN_PATH'}
all_match=all(v['source_sha256']==v['expected_source_sha256'] and v['object_sha256']==v['expected_object_sha256'] for v in projects) and all(v['match'] for v in externals+deps+ir) and all(toolchain.values()) and env['LEAN_PATH']==str(p/'objects')+':'+str(p/'external')
print(json.dumps(dict(projects=projects,dependencies=deps,external=externals,ir=ir,toolchain=toolchain,LEAN_PATH=env['LEAN_PATH'],all_match=all_match)))
'''
payload=json.dumps(dict(workspace=plan['workspace'],pins=plan['modules'],accepted=accepted,external=external,ir=irs))
for retry in range(11):
 r=subprocess.run(['ssh','dombarker@100.108.41.90','python3 -c '+shlex.quote(code)],input=payload,text=True,capture_output=True)
 if r.returncode!=255:break
 (E/f'preflight-transport-{time.time_ns()}.json').write_text(json.dumps(dict(retry=retry,exit=255,stderr=r.stderr),indent=2)+'\n')
 if retry==10:raise RuntimeError('ten preflight transport retries exhausted')
 print('preflight transport cooldown60s',flush=True);time.sleep(60)
assert r.returncode==0,r.stderr
out=json.loads(r.stdout);(E/'fresh-preflight.json').write_text(json.dumps(out,indent=2)+'\n');assert out['all_match']
print('Fresh preflight:',len(out['projects']),'projects,',len(out['dependencies']),'direct fingerprints,',len(out['external']),'external objects,',len(out['ir']),'IR companions; all match')
