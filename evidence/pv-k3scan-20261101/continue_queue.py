"""Continue unchanged logical jobs with fresh IDs after refused admissions."""
from pathlib import Path
import subprocess,json,time,datetime,sys
E=Path(__file__).resolve().parent;H='dombarker@100.108.41.90';R='/home/dombarker/project-offloads/codex-pv-k3scan-20261101';rev=subprocess.check_output(['git','rev-parse','HEAD'],text=True).strip();ident=int(sys.argv[1]);jobs=sys.argv[2:];records=[]
prior=json.loads((E/'D549-QUEUE-K79220.json').read_text())[-1];assert prior['id']=='K79230'and prior['exit']==78
not_before=datetime.datetime.fromisoformat(prior['utc']).timestamp()+180
for job in jobs:
 for retry in range(10):
  assert ident<=79299,'assigned ID block exhausted'
  raw=subprocess.check_output(['ssh',H,'cat '+R+'/last-launch.json']);not_before=max(not_before,json.loads(raw)['epoch']+180)
  while time.time()<not_before:time.sleep(min(30,not_before-time.time()))
  label='K'+str(ident);cfg=json.loads((E/('config-'+job+'.json')).read_text());cmd=f'PV_SOURCE_REVISION={rev} python3 {R}/resume_symbols.py {label} config-{job}.json';r=subprocess.run(['ssh',H,cmd],capture_output=True,text=True)
  rec={'id':label,'logical_job':job,'config_file':'config-'+job+'.json','utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'exit':r.returncode,'stdout':r.stdout,'stderr':r.stderr,'retry_index':retry};records.append(rec);(E/'D549-CONTINUATION-QUEUE.json').write_text(json.dumps(records,indent=2)+'\n');print(label,job,r.returncode,flush=True)
  if r.returncode==255:raise SystemExit('Transport failed after possible submission; recover read-only, never resubmit')
  subprocess.run(['scp','-r',H+':'+R+'/'+label,str(E/'host')],check=True)
  ident+=1
  if r.returncode==78:
   not_before=time.time()+180;continue
  log=(E/'host'/label/'output.log').read_text()
  if cfg.get('negative'):assert r.returncode==1 and 'VERIFICATION:- FAILED'in log and 'Failed Checks:'in log and ('assertion failed:'in log or 'core::panicking::assert_failed_inner'in log),(label,log[-1500:])
  else:assert r.returncode==0 and 'VERIFICATION:- SUCCESSFUL'in log,(label,log[-1500:])
  break
 else:raise SystemExit('Ten refused admissions for this logical job; retain all receipts and resume compile-free work')
