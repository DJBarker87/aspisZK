"""Sequential own launches, retained cooldown and fail-closed admission. No background host scope."""
from pathlib import Path
import subprocess,json,time,sys,datetime
E=Path(__file__).resolve().parent;H='dombarker@100.108.41.90';R='/home/dombarker/project-offloads/codex-pv-k3scan-20261101';rev=subprocess.check_output(['git','rev-parse','HEAD'],text=True).strip();records=[]
for ident in sys.argv[1:]:
 for retry in range(10):
  raw=subprocess.check_output(['ssh',H,'cat '+R+'/last-launch.json']);not_before=json.loads(raw)['epoch']+180
  while time.time()<not_before:time.sleep(min(30,not_before-time.time()))
  cmd=f'PV_SOURCE_REVISION={rev} python3 {R}/resume_symbols.py {ident} config-{ident}.json'
  r=subprocess.run(['ssh',H,cmd],capture_output=True,text=True);v={'id':ident,'utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'exit':r.returncode,'stdout':r.stdout,'stderr':r.stderr};records.append(v);(E/'SYMBOLS-QUEUE.json').write_text(json.dumps(records,indent=2)+'\n');print(ident,r.returncode,flush=True)
  subprocess.run(['scp','-r',H+':'+R+'/'+ident,str(E/'host')],check=True)
  if r.returncode==78:
   print('Refused; queue stops for next-unused-ID rescheduling after cooldown',flush=True);raise SystemExit(78)
  if r.returncode==255:
   print('Transport loss after submission: read-only recovery required, no resubmission',flush=True);raise SystemExit(255)
  cfg=json.loads((E/f'config-{ident}.json').read_text());log=(E/'host'/ident/'output.log').read_text()
  if cfg.get('negative'):
   assert r.returncode==1 and 'VERIFICATION:- FAILED' in log and 'Failed Checks: assertion failed:' in log,(ident,log[-1500:])
  else:assert r.returncode==0 and 'VERIFICATION:- SUCCESSFUL' in log,(ident,log[-1500:])
  break
