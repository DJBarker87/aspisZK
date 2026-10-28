from pathlib import Path
import subprocess,json,sys,time
E=Path(__file__).resolve().parent;a=sys.argv[1]
code=f'''from pathlib import Path
import subprocess,json
b=Path('/home/dombarker/project-offloads/codex-cx-native-tx2m-20261028')
p=subprocess.run(['pgrep','-af',{a!r}],capture_output=True,text=True)
names=[{(a+'.json')!r},{(a+'/receipt.json')!r},{(a+'/stdout.log')!r},{(a+'/time.log')!r},{(a+'-submission.log')!r},{(a+'-submitted.json')!r}]
print(json.dumps(dict(files={{n:(b/n).read_text() for n in names if (b/n).is_file()}},processes=[l for l in p.stdout.splitlines() if 'pgrep' not in l])))
'''
for trial in range(11):
 r=subprocess.run(['ssh','-o','ConnectTimeout=15','-o','ServerAliveInterval=15','-o','ServerAliveCountMax=2','dombarker@100.108.41.90','python3'],input=code,capture_output=True,text=True)
 with (E/(a+'-recovery-transport.jsonl')).open('a') as f:f.write(json.dumps(dict(trial=trial,exit=r.returncode,stdout=r.stdout,stderr=r.stderr))+'\n')
 if r.returncode==0:break
 if r.returncode!=255 or trial==10:raise SystemExit('STOP recovery transport exhausted')
 time.sleep(60)
out=json.loads(r.stdout);(E/(a+'-recovered.json')).write_text(json.dumps(out,indent=2)+'\n')
for n,s in out['files'].items():
 if '/' in n:
  p=E/n;p.parent.mkdir(parents=True,exist_ok=True);p.write_text(s)
print(json.dumps(dict(processes=out['processes'],files=list(out['files']))))
