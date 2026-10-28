"""Verify final private source/object cohort and retrieve original new receipts."""
from pathlib import Path
import subprocess,json,hashlib,re,shlex,lzma
R=Path(__file__).resolve().parents[2];E=R/'evidence/pv-rjdec-20261028';H='/home/dombarker/project-offloads/codex-pv-rjdec-20261028'
sha=lambda b:hashlib.sha256(b).hexdigest();runs=[]
for p in sorted(E.glob('modules-*.json')):
 for v in json.loads(p.read_text()):runs.append(v|{'attempt':int(p.stem.split('-')[-1])})
accepted={v['module']:v for v in runs if v['accepted']};checks=[]
for v in runs:
 pin=v['source'];b=subprocess.check_output(['git','show',v['source_revision']+':'+pin['path']]);assert sha(b)==v['source_sha256'],v['module']
 if v['accepted']:
  assert sha(subprocess.check_output(['git','show','HEAD:'+pin['path']]))==v['source_sha256'],v['module']
  assert not any(x in ' '.join(v['axioms']) for x in ['sorryAx','Lean.ofReduceBool'])
 checks.append(dict(attempt=v['attempt'],module=v['module'],accepted=v['accepted'],source_sha256=sha(b)))
new=[v for v in runs if 61800<=v['attempt']<=61899]
receipts=[json.loads(p.read_text()) for p in E.glob('receipt-618*.json')]
for r in receipts:
 assert r['reservation']['allowed'] is True and r['launch_admission']['allowed'] is True
 assert len(r['modules'])==1 and r['swaps']==0
code=r'''import pathlib,json,sys,hashlib
x=json.load(sys.stdin);p=pathlib.Path(x['H']);env=json.load(open(p/'J.json'));roots=[pathlib.Path(q) for q in env['LEAN_PATH'].split(':')];sha=lambda q:hashlib.sha256(q.read_bytes()).hexdigest();checks=[];deps=[]
for m,v in x['accepted'].items():
 rel=m.replace('.','/');s=p/'sources'/(rel+'.lean');o=p/'objects'/(rel+'.olean');assert sha(s)==v['source_sha256'] and sha(o)==v['object_sha256'],m
 checks.append(dict(module=m,source_sha256=sha(s),object_sha256=sha(o)))
 for d,old in v['dependencies'].items():
  q=next((root/(d.replace('.','/')+'.olean') for root in roots if (root/(d.replace('.','/')+'.olean')).is_file()),None);assert q and sha(q)==old['sha256'],(m,d)
  deps.append(dict(module=m,dependency=d,sha256=sha(q)))
logs={str(q):pathlib.Path(q).read_text() for q in x['files']}
print(json.dumps(dict(checks=checks,dependencies=deps,logs=logs,LEAN_PATH=env['LEAN_PATH'],toolchain=env['LEAN_GITHASH'],all_match=True)))
'''
payload=dict(H=H,accepted=accepted,files=[v[k] for v in new for k in ['output_path','time_path']])
r=subprocess.run(['ssh','dombarker@100.108.41.90','python3 -c '+shlex.quote(code)],input=json.dumps(payload),text=True,capture_output=True);assert r.returncode==0,r.stderr;x=json.loads(r.stdout);logs=x.pop('logs');loghash=[]
for name,s in logs.items():
 q=E/Path(name).name;q.write_text(s);loghash.append(dict(path=str(q.relative_to(R)),sha256=sha(s.encode())))
(E/'d420-own-validation.json').write_text(json.dumps(x,indent=2)+'\n');(E/'d420-source-validation.json').write_text(json.dumps(checks,indent=2)+'\n');(E/'d420-original-logs.json').write_text(json.dumps(loghash,indent=2)+'\n')
summary=dict(attempts=len(new),accepted=sum(v['accepted'] for v in new),rejected=sum(not v['accepted'] for v in new),native_scopes=0,Kani=0,VOID=0,used_IDs=[v['attempt'] for v in new],unused_IDs=sorted(set(range(61800,61900))-{v['attempt'] for v in new}),peak_RSS_bytes=max(v['peak_rss_bytes'] for v in new),swaps=sum(v['swaps'] for v in new),all_sources_objects_and_imports_match=True,axioms=[line for v in new if v['accepted'] for line in v['axioms']])
(E/'d420-validation.json').write_text(json.dumps(summary,indent=2)+'\n');print(json.dumps({k:v for k,v in summary.items() if k not in ['axioms','used_IDs','unused_IDs']}))
for q in E.rglob('*'):
 if q.is_file() and q.stat().st_size>20_000_000:
  b=q.read_bytes();q.with_name(q.name+'.xz').write_bytes(lzma.compress(b));q.with_name(q.name+'.sha256').write_text(sha(b)+'\n');q.unlink()
