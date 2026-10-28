"""Collect exact evidence and validate accepted source/object/import identities."""
from pathlib import Path
import subprocess,json,hashlib,re,shlex,lzma
R=Path(__file__).resolve().parents[2];E=R/'evidence/pv-rjdec-20261028';H='/home/dombarker/project-offloads/codex-pv-rjdec-20261028';host='dombarker@100.108.41.90'
sha=lambda b:hashlib.sha256(b).hexdigest();receipts=[json.loads(p.read_text()) for p in sorted(E.glob('receipt-*.json'))];runs=[v|{'attempt':int(p.stem.split('-')[-1])} for p in sorted(E.glob('modules-*.json')) for v in json.loads(p.read_text())];accepted={v['module']:v for v in runs if v['accepted']};failed=[];checked=[]
for v in runs:
 pin=v['source'];b=subprocess.check_output(['git','show',v['source_revision']+':'+pin['path']]);assert sha(b)==v['source_sha256']
 if v['accepted']:
  now=subprocess.check_output(['git','show','HEAD:'+pin['path']]);assert sha(now)==v['source_sha256'],v['module'];assert not any(a in ' '.join(v['axioms']) for a in ['sorryAx','Lean.ofReduceBool'])
 else:failed.append({k:v[k] for k in ['attempt','module','source_revision','source_sha256','source']})
 checked.append(dict(attempt=v['attempt'],module=v['module'],source_sha256=sha(b),accepted=v['accepted']))
for r in receipts:
 assert r['reservation']['allowed'] is True and r['launch_admission']['allowed'] is True and r['swaps']==0 and len(r['modules'])==1
 assert 61300<=r['attempt']<=61399
payload=dict(H=H,accepted=accepted,files=[v[k] for v in runs for k in ['output_path','time_path']])
code=r'''import json,pathlib,sys,hashlib
x=json.load(sys.stdin);p=pathlib.Path(x['H']);env=json.load(open(p/'J.json'));roots=[pathlib.Path(q) for q in env['LEAN_PATH'].split(':')];sha=lambda q:hashlib.sha256(q.read_bytes()).hexdigest();checks=[];deps=[]
for m,v in x['accepted'].items():
 rel=m.replace('.','/');s=p/'sources'/(rel+'.lean');o=p/'objects'/(rel+'.olean');assert sha(s)==v['source_sha256'] and sha(o)==v['object_sha256'],m
 checks.append(dict(module=m,source_sha256=sha(s),object_sha256=sha(o)))
 for d,old in v['dependencies'].items():
  q=next((root/(d.replace('.','/')+'.olean') for root in roots if (root/(d.replace('.','/')+'.olean')).is_file()),None);assert q and sha(q)==old['sha256'],(m,d);deps.append(dict(module=m,dependency=d,sha256=sha(q)))
logs={str(q):pathlib.Path(q).read_text() for q in x['files']}
print(json.dumps(dict(checks=checks,dependencies=deps,logs=logs,LEAN_PATH=env['LEAN_PATH'],toolchain=env['LEAN_GITHASH'],all_match=True)))
'''
r=subprocess.run(['ssh',host,'python3 -c '+shlex.quote(code)],input=json.dumps(payload),text=True,capture_output=True);assert r.returncode==0,r.stderr;result=json.loads(r.stdout);logs=result.pop('logs');loghash=[]
for path,txt in logs.items():
 q=E/Path(path).name;q.write_text(txt);loghash.append(dict(path=str(q.relative_to(R)),sha256=sha(txt.encode())))
(E/'resume-original-logs.json').write_text(json.dumps(loghash,indent=2)+'\n');(E/'resume-own-validation.json').write_text(json.dumps(result,indent=2)+'\n');(E/'resume-source-validation.json').write_text(json.dumps(checked,indent=2)+'\n');(E/'resume-failed-sources.json').write_text(json.dumps(failed,indent=2)+'\n')
launched={r['attempt'] for r in receipts}|{61307,61311};unused=sorted(set(range(61300,61400))-launched)
summary=dict(Lean_attempts=len(receipts),resume_Lean_attempts=sum(r['attempt']<61397 and r['attempt']>=61312 for r in receipts),accepted=sum(r['accepted'] for r in receipts),rejected=sum(not r['accepted'] for r in receipts),native_scopes=2,resume_native_scopes=0,Kani=0,void_attempts=0,unused_IDs=unused,peak_Lean_RSS_bytes=max(r['peak_rss_bytes'] for r in receipts),swaps=0,axioms=[a for v in accepted.values() for a in v['axioms']],all_accepted_pins_match=True)
(E/'resume-validation.json').write_text(json.dumps(summary,indent=2)+'\n');print(json.dumps({k:v for k,v in summary.items() if k!='axioms'}))
# Explicitly identify staged or drafted sources that did not receive proof credit.
plan=json.loads((E/'build-plan.json').read_text());uncredited={m:v for m,v in plan['modules'].items() if m.startswith('R1Z.PV_RJDec_') and m not in accepted};(E/'resume-uncredited-sources.json').write_text(json.dumps(uncredited,indent=2)+'\n')
for q in E.rglob('*'):
 if q.is_file() and q.stat().st_size>20_000_000:
  b=q.read_bytes();q.with_name(q.name+'.xz').write_bytes(lzma.compress(b));q.with_name(q.name+'.sha256').write_text(sha(b)+'\n');q.unlink()
