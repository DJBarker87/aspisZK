"""Collect original logs and verify every accepted source/import, without replay."""
from pathlib import Path
import json,subprocess,hashlib,shlex,re
E=Path('evidence/pv-rj4id-20261029');H='/home/dombarker/project-offloads/codex-pv-rj4id-20261029';sha=lambda b:hashlib.sha256(b).hexdigest();runs=[]
for f in sorted(E.glob('modules-644*.json')):
 for v in json.loads(f.read_text()):runs.append(v|dict(attempt=int(f.stem.split('-')[-1])))
accepted={v['module']:v for v in runs if v['accepted']}
for v in runs:
 b=subprocess.check_output(['git','show',v['source_revision']+':'+v['source']['path']]);assert sha(b)==v['source_sha256']
 if v['accepted']:assert sha(subprocess.check_output(['git','show','HEAD:'+v['source']['path']]))==v['source_sha256']
for r in [json.loads(f.read_text()) for f in E.glob('receipt-644*.json')]:
 assert r['reservation']['allowed'] and r['launch_admission']['allowed'] and r['swaps']==0
 assert r['command'].count('MemoryHigh=6G')==1 and r['command'].count('MemoryMax=8G')==1 and r['command'].count('MemorySwapMax=0')==1
 assert len(r['modules'])==1
code=r'''import json,pathlib,sys,hashlib
x=json.load(sys.stdin);p=pathlib.Path(x['H']);env=json.load(open(p/'J.json'));roots=[pathlib.Path(q) for q in env['LEAN_PATH'].split(':')];sha=lambda q:hashlib.sha256(q.read_bytes()).hexdigest();checks=[]
for m,v in x['accepted'].items():
 assert sha(p/'sources'/(m+'.lean'))==v['source_sha256'];assert sha(p/'objects'/(m+'.olean'))==v['object_sha256']
 for d,old in v['dependencies'].items():
  q=next(root/(d.replace('.','/')+'.olean') for root in roots if (root/(d.replace('.','/')+'.olean')).is_file());assert sha(q)==old['sha256'],(m,d)
 checks.append(dict(module=m,source_sha256=v['source_sha256'],object_sha256=v['object_sha256'],deps_fingerprint=v['deps_fingerprint']))
logs={q:pathlib.Path(q).read_text() for q in x['files']}
print(json.dumps(dict(all_match=True,checks=checks,logs=logs,toolchain=env['LEAN_GITHASH'],LEAN_PATH=env['LEAN_PATH'])))
'''
payload=dict(H=H,accepted=accepted,files=[v[k] for v in runs for k in ['output_path','time_path']])
r=subprocess.run(['ssh','dombarker@100.108.41.90','python3 -c '+shlex.quote(code)],input=json.dumps(payload),text=True,capture_output=True);assert r.returncode==0,r.stderr
x=json.loads(r.stdout);logs=x.pop('logs');original=[]
for name,s in logs.items():
 f=E/Path(name).name;f.write_text(s);original.append(dict(path=str(f),sha256=sha(s.encode())))
(E/'final-validation.json').write_text(json.dumps(x|dict(original_logs=original),indent=2)+'\n')
allowed={'propext','Classical.choice','Quot.sound'}
axioms=[line for v in accepted.values() for line in v['axioms']]
for line in axioms:
 if 'depends on axioms:' in line:
  found=set(re.search(r'\[([\s\S]*?)\]',line)[1].replace('\n',' ').replace(' ','').split(','));assert found<=allowed,(line,found)
summary=dict(attempts=len(runs),accepted=sum(v['accepted'] for v in runs),rejected=sum(not v['accepted'] for v in runs),native_scopes=0,Kani=0,VOID=0,ids=[v['attempt'] for v in runs],source_revisions={str(v['attempt']):v['source_revision'] for v in runs},peak_rss_bytes=max(v['peak_rss_bytes'] for v in runs),swaps=sum(v['swaps'] for v in runs),axioms=axioms,endpoint_premises_removed=0)
(E/'summary.json').write_text(json.dumps(summary,indent=2)+'\n');print(json.dumps({k:v for k,v in summary.items() if k not in ['axioms','source_revisions','ids']}))
with (E/'receipts.md').open('w') as f:
 f.write('| ID | Exact target | Exit | Wall s | Peak RSS bytes | Swap | Source revision | Axioms |\n|---|---|---:|---:|---:|---:|---|---|\n')
 for v in runs:
  ax='standard only' if v['accepted'] else 'rejected; no credit'
  f.write(f"| {v['attempt']} | `{v['module']}` | {v['exit']} | {v['wall_seconds']} | {v['peak_rss_bytes']} | {v['swaps']} | `{v['source_revision']}` | {ax} |\n")
subprocess.run(['git','log','--oneline','60a288b546..HEAD'],stdout=(E/'COMMITS.txt').open('w'),check=True)
