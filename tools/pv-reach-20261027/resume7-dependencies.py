"""Build source-authorized inherited prerequisites in dependency order privately.
Never follows output symlinks; never imports another job's h5 object.
"""
import pathlib,json,subprocess,shlex,hashlib,sys,time
R=pathlib.Path(__file__).resolve().parents[2];E=R/'evidence/pv-reach-20261027/resume7';H='/home/dombarker/project-offloads/codex-pv-reach-20261027/lean';host='dombarker@100.108.41.90'
rows=json.loads((E/'project-closure.json').read_text());mapping={r['module']:r for r in rows};a=int(sys.argv[1]);limit=int(sys.argv[2])
# Only HEAD-source h5 modules; exact originals are retained, no import edits.
script='''import pathlib,json,sys,hashlib
rows=json.load(sys.stdin);e=json.load(open('/home/dombarker/project-offloads/codex-pv-reach-20261027/lean/J.json'));roots=[pathlib.Path(x) for x in e['LEAN_PATH'].split(':')];out=[]
for r in rows:
 rel=pathlib.Path(*r['module'].split('.')).with_suffix('.olean');p=next((x/rel for x in roots if (x/rel).is_file()),None)
 out.append(dict(module=r['module'],object_exists=p is not None,path=str(p),sha256=hashlib.sha256(p.read_bytes()).hexdigest() if p else None))
print(json.dumps(out))
'''
p=subprocess.run(['ssh',host,'python3 -c '+shlex.quote(script)],input=json.dumps(rows),capture_output=True,text=True,check=True);available={r['module']:r['object_exists'] for r in json.loads(p.stdout)};(E/'effective-project-cache.json').write_text(p.stdout)
private={r['target'].replace('/','.') for p in E.parent.rglob('receipt-[0-9]*.json') if (r:=json.loads(p.read_text())).get('accepted') and r.get('source_sha256')==mapping.get(r['target'].replace('/','.'),{}).get('sha256') and available.get(r['target'].replace('/','.'),False)}
selected=[]
for r in rows:
 if a>=limit:break
 m=r['module']
 if m in private or (r['authority']!='h5' and available.get(m,False)):continue
 old=[json.loads(p.read_text()) for p in E.glob('receipt-[0-9]*.json') if json.loads(p.read_text())['target'].replace('/','.')==m]
 if old:
  if not (E/'pinned-cache-links.json').exists():continue
  restored={x['module'] for x in json.loads((E/'pinned-cache-links.json').read_text())['restored']}
  failures=[x for x in old if not x['accepted']]
  import re
  missing_names=[]
  for x in failures:
   text=(E/f"out-{x['attempt']}.log").read_text()
   missing_names+=re.findall(r"of module ([A-Za-z0-9_.]+) does not exist",text)
  if not missing_names or not set(missing_names)<=restored:continue
 # A source module is attempted only once all direct h5 dependencies are private.
 def h5_predecessors(n,seen=None):
  seen=set() if seen is None else seen
  for d in mapping[n]['imports']:
   if d in mapping and d not in seen:
    seen.add(d);h5_predecessors(d,seen)
  return {d for d in seen if mapping[d]['authority']=='h5'}
 missing=sorted(h5_predecessors(m)-private)
 if missing:
  selected.append(dict(module=m,status='pending_h5_predecessors',missing=missing));continue
 missing=[d for d in r['imports'] if d in mapping and not available.get(d,True)]
 if missing:
  selected.append(dict(module=m,status='pending_missing_pinned_dependencies',missing=missing));continue
 src=R/r['path']
 if r['authority']!='h5':
  src=E/'authorized-sources'/(m+'.lean.txt');src.parent.mkdir(exist_ok=True)
  src.write_bytes(subprocess.check_output(['git','show',r['blob']]))
 assert hashlib.sha256(src.read_bytes()).hexdigest()==r['sha256']
 # run2 emits .olean and companion files; detach only this job's symlinks.
 code=f'''import pathlib,json
p=pathlib.Path({H!r})/'objects'/pathlib.Path({m.replace('.','/')!r});removed=[]
for q in p.parent.glob(p.name+'.*'):
 if q.is_symlink():removed.append(dict(path=str(q),target=str(q.readlink())));q.unlink()
print(json.dumps(removed))
'''
 q=subprocess.run(['ssh',host,'python3 -c '+shlex.quote(code)],capture_output=True,text=True,check=True)
 (E/f'private-detach-{a}.json').write_text(q.stdout)
 q=subprocess.run([sys.executable,str(R/'tools/pv-reach-20261027/resume7-check.py'),str(a),m.replace('.','/'),str(src.relative_to(R))],capture_output=True,text=True)
 receipt=E/f'receipt-{a}.json'
 if not receipt.exists():
  print(q.stdout+q.stderr,flush=True)
  if q.returncode==78:
   # Refusal consumes ID only. Keep work item and retry after 3 minutes.
   # Caller resumes from its next unspent ID; no unchanged compile occurred.
   sys.exit(78)
  sys.exit(2)
 result=json.loads(receipt.read_text());selected.append(dict(module=m,attempt=a,accepted=result['accepted']));print(json.dumps(selected[-1]),flush=True)
 if not result['accepted']:print(q.stdout[-2500:]+q.stderr[-500:],flush=True)
 if result['exit'] is None:sys.exit(2)
 if result['accepted']:private.add(m);available[m]=True
 a+=1
 (E/'dependency-progress.json').write_text(json.dumps(dict(next_id=a,steps=selected,private_h5=sorted(private)),indent=2)+'\n')
print('NEXT',a,flush=True)
