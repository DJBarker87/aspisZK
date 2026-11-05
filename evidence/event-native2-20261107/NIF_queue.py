from pathlib import Path
import subprocess,sys,json,re
E=Path(__file__).resolve().parent
start=int(sys.argv[1]);names=sys.argv[2:]
for offset,name in enumerate(names):
 a=f'NIF_K{start+offset:03d}'
 r=subprocess.run([sys.executable,str(E/'NIF_kani_run.py'),a,'kani',name],capture_output=True,text=True)
 (E/(a+'-client.log')).write_text(r.stdout+r.stderr)
 p=E/a/'stdout.log';s=p.read_text() if p.exists() else ''
 status='TIMEOUT' if re.search('TIMEOUT|CBMC timed out',s) else 'PASS' if 'VERIFICATION:- SUCCESSFUL' in s or 'VERIFICATION:- SUCCESS' in s or 'VERIFICATION:- SUCCESSFUL' in s else 'FAIL' if 'VERIFICATION:- FAILED' in s else 'OTHER'
 with (E/'NIF_QUEUE.jsonl').open('a') as f:f.write(json.dumps(dict(attempt=a,harness=name,exit=r.returncode,status=status))+'\n')
 print(a,name,status,flush=True)
 if status in ['TIMEOUT','OTHER']:
  print('review required before continuation',flush=True);sys.exit(2)
