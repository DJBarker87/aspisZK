from pathlib import Path
import subprocess,json,time,hashlib,os,re
w=Path('/home/dombarker/project-offloads/aspis-r1-r18-tools-20261016');name='aspis-r18-tools-20261016-a'
cap={'memory.high':str(6*2**30),'memory.max':str(8*2**30),'memory.swap.max':'0'}
run=lambda a:subprocess.check_output(a,text=True).strip()
state=json.loads(run(['docker','inspect',name]))[0];assert state['State']['Status']=='created'
assert state['Image']=='sha256:ef96e46342a4159b6a62663e1ff5474a5f5deaf260daf08ea7b0963974418db7'
assert not (w/'aeneas-go').exists();out=w/'aeneas-build-a';out.mkdir(exist_ok=False)
(out/'container-before.json').write_text(json.dumps(state,indent=2)+'\n')
run(['docker','start',name]);state=json.loads(run(['docker','inspect',name]))[0];pid=state['State']['Pid'];cid=state['Id']
rel=next(x.split(':',2)[2] for x in Path(f'/proc/{pid}/cgroup').read_text().splitlines() if x.startswith('0::'))
assert cid in rel,rel;cg=Path('/sys/fs/cgroup')/rel.lstrip('/')
unit='docker-'+cid+'.scope'
subprocess.check_call(['sudo','-n','systemctl','set-property','--runtime',unit,'MemoryHigh=6G','MemoryMax=8G','MemorySwapMax=0'])
read=lambda p:p.read_text().strip()
assert {k:read(cg/k) for k in cap}==cap
pre={'container':cid,'image':state['Image'],'host_pid':pid,'actual_cgroup':str(cg),'limits':cap,'memory_events_before':read(cg/'memory.events'),'command':['bash','/work/build-aeneas.sh'],'source_archives':json.loads((w/'inputs/source-archives.json').read_text()),'script_sha256':hashlib.sha256((w/'build-aeneas.sh').read_bytes()).hexdigest(),'root_filesystem_readonly':True,'network':'none','scope_note':'The compiler container itself is capped; no separate capped Docker CLI scope.'}
(out/'preflight.json').write_text(json.dumps(pre,indent=2)+'\n')
(w/'aeneas-go').write_text('actual container cgroup verified before compiler start\n')
begin=time.monotonic();peak=0;examples={};timedout=False;last={}
while True:
 state=json.loads(run(['docker','inspect',name]))[0]
 if not state['State']['Running']:break
 if cg.exists():
  peak=max(peak,int(read(cg/'memory.current')))
  last={k:read(cg/k) for k in ['memory.current','memory.peak','memory.swap.current','memory.events']}
  for line in read(cg/'cgroup.procs').splitlines():
   try:
    proc=Path('/proc')/line;cmd=(proc/'cmdline').read_bytes().replace(b'\0',b' ').decode(errors='replace')
    if any(x in cmd for x in ['ocamlopt','ocamlc','dune','gcc','/cc ']):
     loc=read(proc/'cgroup');assert cid in loc
     key=next(x for x in ['ocamlopt','ocamlc','dune','gcc','/cc '] if x in cmd)
     examples.setdefault(key,{'pid':int(line),'command':cmd,'actual_cgroup':loc,'limits':{k:read(cg/k) for k in cap}})
   except (FileNotFoundError,ProcessLookupError):pass
 if time.monotonic()-begin>600:
  subprocess.check_call(['docker','stop','-t','5',name]);timedout=True;break
 time.sleep(.2)
state=json.loads(run(['docker','inspect',name]))[0];rc=state['State']['ExitCode']
(out/'container-after.json').write_text(json.dumps(state,indent=2)+'\n')
(out/'container.log').write_text(run(['docker','logs',name]))
r={**pre,'exit_status':rc,'wall_seconds':round(time.monotonic()-begin,3),'sampled_cgroup_peak_bytes':peak,'last_cgroup_observation':last,'compiler_process_examples':examples,'ten_minute_review_stop':timedout,'time_reports':{}}
for n in ['charon-ml','aeneas']:
 p=out/(n+'.time')
 if p.exists():
  s=p.read_text();d={}
  for key,label in [('peak_process_rss_kib','Maximum resident set size (kbytes)'),('process_swaps','Swaps')]:
   m=re.search(re.escape(label)+r':\s*(\d+)',s);d[key]=int(m[1]) if m else None
  r['time_reports'][n]=d
if rc==0:r['binary_sha256']=hashlib.sha256((w/'bin/aeneas').read_bytes()).hexdigest()
(out/'receipt.json').write_text(json.dumps(r,indent=2)+'\n');print(json.dumps({k:r[k] for k in ['exit_status','wall_seconds','sampled_cgroup_peak_bytes','time_reports','ten_minute_review_stop']},indent=2))
raise SystemExit(rc)
