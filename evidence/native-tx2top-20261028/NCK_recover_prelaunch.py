from pathlib import Path
import json,subprocess,time
E=Path(__file__).resolve().parent
attempt='NCK_L057';module='NCK_AuthenticationCuts'
code=f'''from pathlib import Path
import json,subprocess
b=Path('/home/dombarker/project-offloads/codex-cx-native-tx2top-20261028')
paths={[attempt+'.json','NCK_generated/'+module+'.lean',attempt+'/receipt.json']!r}
o={{n:(b/n).exists() for n in paths}}
o['units']=subprocess.run(['systemctl','--user','list-units','--type=scope','--no-pager','--all'],capture_output=True,text=True).stdout
print(json.dumps(o))
'''
for retry in range(1,10):
 time.sleep(60)
 r=subprocess.run(['ssh','-o','ConnectTimeout=15','-o','ServerAliveInterval=15','-o','ServerAliveCountMax=2','dombarker@100.108.41.90','python3'],input=code,capture_output=True,text=True)
 with (E/'NCK_L057_RECOVERY_RETRIES.jsonl').open('a') as f:f.write(json.dumps(dict(retry=retry,exit=r.returncode,stdout=r.stdout,stderr=r.stderr,read_only=True))+'\n')
 print('read-only recovery',retry,'exit',r.returncode,flush=True)
 if r.returncode==255:continue
 assert r.returncode==0,r.stderr
 o=json.loads(r.stdout)
 assert all(o[n] is False for n in [attempt+'.json','NCK_generated/'+module+'.lean',attempt+'/receipt.json']),'inputs/receipt now exist; recover only, do not resubmit'
 assert attempt+'.json' not in o['units']
 p=E/'NCK_ACTIVE.json';x=json.loads(p.read_text());assert x['attempt']==attempt;x['submitted']=False;x['confirmed_prelaunch_failures']=2;x['recovery_retry']=retry;p.write_text(json.dumps(x)+'\n')
 (E/'NCK_L057_PRELAUNCH_FINAL.json').write_text(json.dumps(dict(classification='confirmed never uploaded/launched',read_only=o,transport_retries=retry,submission_failures=2),indent=2)+'\n')
 break
else:raise SystemExit('STOP persistent transport outage; no resubmission')
