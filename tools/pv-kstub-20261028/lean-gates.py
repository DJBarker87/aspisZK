from pathlib import Path
import subprocess,json,time,sys
R=Path(__file__).resolve().parents[2];E=R/'evidence/pv-kstub-20261028';D='/home/dombarker/project-offloads/codex-pv-kstub-20261028'
for p in json.loads((E/'lean-plan.json').read_text()):
 n=str(p['id']);m=p['module']
 cmd=['timeout','900','python3','/home/dombarker/project-offloads/aspis-fs-generic-20261006/evidence/run2.py',D+'/env-J.json',D+'/lean-objects',D,D+'/lean-objects/'+m+'.olean',D+'/'+m+'.lean','7000']
 assert not (E/n/'receipt.json').exists()
 for k in range(11):
  q=subprocess.run([sys.executable,str(R/'tools/pv-kstub-20261028/scope.py'),n,'Lean',*cmd])
  if q.returncode!=78:break
  if k<10:time.sleep(180)
 if q.returncode:sys.exit(q.returncode)
 f=E/n/'receipt.json';r=json.loads(f.read_text());r.update(p);r['external_preflight']='lean-external-preflight.json';f.write_text(json.dumps(r,indent=2)+'\n')
