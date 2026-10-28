from pathlib import Path
import sys,json,subprocess,importlib.util,shlex,hashlib,time
E=Path(__file__).resolve().parent
args=sys.argv[1:];sys.argv=['ncc','none'];s=importlib.util.spec_from_file_location('ncc',E/'NCC_native.py');m=importlib.util.module_from_spec(s);s.loader.exec_module(m)
start=int(args[0]);hs=args[1:];assert start+len(hs)-1<=60
m.admit('NCC_BATCH'+str(start)+'_UPLOAD')
base=json.loads((E/'NCC_K001.json').read_text());items=[]
for i,h in enumerate(hs,start):
 a=f'NCC_K{i:03}';assert not (E/a/'receipt.json').exists();cfg=json.loads(json.dumps(base));cfg.update(attempt=a,module=h,command=['python3','NCC_gate.py',a,h],timeout=600,source_revision=subprocess.check_output(['git','rev-parse','HEAD'],text=True).strip());cfg['sources']=['NCC_gate.py','NCC_frozen_graph.sha256']+[x for x in base['sources'] if x not in ['NCC_gate.py','NCC_frozen_graph.sha256']];cfg['expected_time']='Optimized compilation then named solver gate; metadata validated inside same capped scope';items.append(cfg)
name='NCC_BATCH'+str(start)+'.json'
files={n:(E/n).read_text() for n in ['NCC_gate.py','NCC_batch_host.py']};files['NCC_frozen_graph.sha256']=(E/'NCC_frozen_graph.sha256').read_text();files[name]=json.dumps(dict(base=items[0],targets=[dict(attempt=x['attempt'],module=x['module'],command=x['command']) for x in items]))
payload='from pathlib import Path; b=Path('+repr(m.B)+'); files='+repr(files)+'; [(b/n).write_text(s) for n,s in files.items()]'
for trial in range(11):
 r=subprocess.run(['ssh','-o','ConnectTimeout=15','-o','ServerAliveInterval=15','-o','ServerAliveCountMax=2',m.H,'python3 -'],input=payload,capture_output=True,text=True,timeout=90)
 with (E/'NCC_UPLOAD_TRANSPORT.jsonl').open('a') as f:f.write(json.dumps(dict(batch=name,trial=trial,exit=r.returncode,stdout=r.stdout,stderr=r.stderr,payload_sha256=hashlib.sha256(payload.encode()).hexdigest(),submitted_prover=False))+'\n')
 if r.returncode!=255:break
 if trial<10:time.sleep(60)
assert r.returncode==0,r.stderr
cmd='cd '+shlex.quote(m.B)+' && python3 NCC_batch_host.py '+shlex.quote(name)
with (E/('NCC_BATCH'+str(start)+'-ssh.stderr')).open('w') as err:
 p=subprocess.Popen(['ssh','-o','ConnectTimeout=15','-o','ServerAliveInterval=15','-o','ServerAliveCountMax=2',m.H,cmd],stdout=subprocess.PIPE,stderr=err,text=True)
 for line in p.stdout:
  x=json.loads(line)
  with (E/'NCC_BATCH_EVENTS.jsonl').open('a') as f:f.write(json.dumps({k:v for k,v in x.items() if k not in ['files','launcher']})+'\n')
  a=x['attempt']
  if x['event']=='admission':(E/(a+'-admission-'+str(x['trial'])+'.json')).write_text(json.dumps(x,indent=2))
  elif x['event']=='result':
   for n,s in x['files'].items():q=E/n;q.parent.mkdir(parents=True,exist_ok=True);q.write_text(s)
   (E/(a+'-launcher.log')).write_text(x['launcher']);rc=json.loads(x['files'][a+'/receipt.json'])
   with (E/'NCC_ATTEMPTS.jsonl').open('a') as f:f.write(json.dumps(rc)+'\n')
   print(a,rc['exit_status'],rc['wall_seconds'],rc['peak_rss_kib'],flush=True)
 assert p.wait()==0,'STOP batch transport/controller; recover read-only, never resubmit'
