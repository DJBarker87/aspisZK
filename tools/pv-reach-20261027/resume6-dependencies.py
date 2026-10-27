"""Build source-authorized inherited prerequisites in dependency order privately.
Never follows output symlinks; never imports another job's h5 object.
"""
import pathlib,json,subprocess,shlex,hashlib,sys,time
R=pathlib.Path(__file__).resolve().parents[2];E=R/'evidence/pv-reach-20261027/resume6';H='/home/dombarker/project-offloads/codex-pv-reach-20261027/lean';host='dombarker@100.108.41.90'
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
private={r['target'].replace('/','.') for p in E.glob('receipt-*.json') if (r:=json.loads(p.read_text()))['accepted']}
selected=[]
for r in rows:
 if a>=limit:break
 m=r['module']
 if r['authority']!='h5' or m in private:continue
 # A source module is attempted only once all direct h5 dependencies are private.
 missing=[d for d in r['imports'] if d in mapping and mapping[d]['authority']=='h5' and d not in private]
 if missing:
  selected.append(dict(module=m,status='pending_h5_predecessors',missing=missing));continue
 missing=[d for d in r['imports'] if d in mapping and not available.get(d,True)]
 if missing:
  selected.append(dict(module=m,status='pending_missing_pinned_dependencies',missing=missing));continue
 src=R/r['path'];assert hashlib.sha256(src.read_bytes()).hexdigest()==r['sha256']
 # run2 emits .olean and companion files; detach only this job's symlinks.
 code=f'''import pathlib,json
p=pathlib.Path({H!r})/'objects'/pathlib.Path({m.replace('.','/')!r});removed=[]
for q in p.parent.glob(p.name+'.*'):
 if q.is_symlink():removed.append(dict(path=str(q),target=str(q.readlink())));q.unlink()
print(json.dumps(removed))
'''
 q=subprocess.run(['ssh',host,'python3 -c '+shlex.quote(code)],capture_output=True,text=True,check=True)
 (E/f'private-detach-{a}.json').write_text(q.stdout)
 q=subprocess.run([sys.executable,str(R/'tools/pv-reach-20261027/resume6-check.py'),str(a),m.replace('.','/'),r['path']],capture_output=True,text=True)
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
