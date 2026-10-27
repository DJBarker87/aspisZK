"""Privately check missing source-pinned cohort prerequisites, smallest first."""
import pathlib,json,subprocess,sys,hashlib
R=pathlib.Path(__file__).resolve().parents[2];E=R/'evidence/pv-reach-20261027/resume7'
a=int(sys.argv[1]);limit=int(sys.argv[2]);rows=json.loads((E/'private-closure-availability.json').read_text());progress=[]
available={r['module'] for r in rows if r['private_exists']}
for row in rows:
 if a>limit:break
 if row['private_exists'] or row['authority']=='h5':continue
 m=row['module']
 missing=[d for d in row['imports'] if d in {x['module'] for x in rows} and d not in available]
 if missing:
  progress.append(dict(module=m,pending=missing));continue
 p=E/'authorized-sources'/(m+'.lean.txt');p.parent.mkdir(exist_ok=True);p.write_bytes(subprocess.check_output(['git','show',row['blob']]))
 assert hashlib.sha256(p.read_bytes()).hexdigest()==row['sha256']
 r=subprocess.run([sys.executable,str(R/'tools/pv-reach-20261027/resume7-check.py'),str(a),m.replace('.','/'),str(p.relative_to(R))],capture_output=True,text=True)
 q=E/f'receipt-{a}.json'
 if not q.exists():print(r.stdout+r.stderr,flush=True);sys.exit(r.returncode or 2)
 d=json.loads(q.read_text());progress.append(dict(module=m,attempt=a,accepted=d['accepted']));print(json.dumps(progress[-1]),flush=True)
 if not d['accepted']:print(r.stdout[-1800:]+r.stderr[-500:],flush=True)
 if d['exit'] is None:sys.exit(2)
 if d['accepted']:available.add(m)
 a+=1;(E/'pinned-build-progress.json').write_text(json.dumps(dict(next_id=a,steps=progress),indent=2)+'\n')
print('NEXT',a,flush=True)
