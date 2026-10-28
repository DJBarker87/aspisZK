from pathlib import Path
import sys,json,subprocess
E=Path(__file__).resolve().parent
for a,module in json.loads((E/sys.argv[1]).read_text()):
 assert a.startswith('NBN_L') and int(a[5:])<=100
 out=E/(a+'-console.log')
 with out.open('w') as f:r=subprocess.run([sys.executable,str(E/'NBN_build.py'),a,'lean/'+module+'.lean',module],stdout=f,stderr=subprocess.STDOUT)
 p=E/a/'receipt.json'
 if r.returncode!=0 or not p.exists():raise SystemExit('STOP '+a+' wrapper/receipt; inspect '+str(out))
 x=json.loads(p.read_text());print(a,x['exit_status'],x['wall_seconds'],flush=True)
 if x['exit_status']!=0:raise SystemExit('STOP '+a+' rejected proof; no dependent launch')
 for line in x['print_axioms']:
  if 'depends on axioms' in line:
   names=line.split('[',1)[1].split(']',1)[0].replace(' ','').split(',')
   assert set(names)<=set(['propext','Classical.choice','Quot.sound']),line
