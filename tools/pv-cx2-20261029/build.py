"""One job-owned Docker cgroup, guarded both before creation and at release."""
from pathlib import Path
import datetime,hashlib,json,subprocess,time,re,sys
H=Path('/home/dombarker/project-offloads/codex-pv-cx-20261029/resume-ae1')
G=H.parents[1]/'codex-cx-prover-rw-20261023/native-entropy/reservation.py'
IMAGE='sha256:ef96e46342a4159b6a62663e1ff5474a5f5deaf260daf08ea7b0963974418db7'
n=int(sys.argv[1]);assert 73330<=n<=73349
O=H/f'N{n}';O.mkdir()
name=f'pv-cx2-n{n}'
def admission(label,requested):
 p=O/label
 r=subprocess.run(['python3',str(G),str(p),'--requested-bytes',str(requested)],stdout=subprocess.PIPE,stderr=subprocess.STDOUT,text=True)
 (O/(label+'.log')).write_text(r.stdout)
 x=json.loads(p.read_text());assert r.returncode==0 and x.get('allowed') is True,(r.returncode,x)
admission('reservation-before.json',8*2**30)
cmd=['docker','create','--name',name,'--network','none','--memory','8g','--memory-swap','8g','--pids-limit','64','--cpus','4','--user','0','--mount',f'type=bind,src={H},dst=/job','--entrypoint','/bin/bash',IMAGE,'-c',f'while [ ! -f /job/N{n}/go ]; do sleep 0.1; done; exec /usr/bin/time -v -o /job/N{n}/time.log timeout 540 opam exec -- bash /job/build.sh']
(O/'command.json').write_text(json.dumps(dict(command=cmd,expected_work='Optimized OCaml compilation: pinned Charon dependency then original extended Aeneas translator; no arithmetic gate.',source_revision='570c0008098b8cc23d16d86f9edb0c2a41b0e118',source_recovery_sha256=hashlib.sha256((H/'source-recovery.json').read_bytes()).hexdigest()),indent=2)+'\n')
cid=subprocess.check_output(cmd,text=True).strip()
subprocess.run(['docker','start',cid],check=True,stdout=subprocess.DEVNULL)
info=json.loads(subprocess.check_output(['docker','inspect',cid]))[0]
pid=info['State']['Pid'];cg=Path('/sys/fs/cgroup'+Path(f'/proc/{pid}/cgroup').read_text().split('0::')[1].strip())
subprocess.run(['sudo','-n','tee',str(cg/'memory.high')],input=str(6*2**30),text=True,check=True,stdout=subprocess.DEVNULL)
limits={k:(cg/k).read_text().strip() for k in ['memory.high','memory.max','memory.swap.max','pids.max']}
try:
 assert list(limits.values())==[str(6*2**30),str(8*2**30),'0','64']
 (O/'caps.json').write_text(json.dumps(dict(cgroup=str(cg),limits=limits),indent=2)+'\n')
 admission('reservation-at-barrier.json',0)
except BaseException:
 subprocess.run(['docker','stop','--time','1',cid],check=True,stdout=subprocess.DEVNULL);raise
start=time.monotonic();(O/'go').touch()
w=subprocess.Popen(['docker','wait',cid],stdout=subprocess.PIPE,text=True);peaks={}
while w.poll() is None:
 for k in ['memory.peak','memory.swap.peak','pids.peak']:
  try:peaks[k]=max(peaks.get(k,0),int((cg/k).read_text()))
  except FileNotFoundError:pass
 time.sleep(.1)
rc=int(w.communicate()[0]);(O/'output.log').write_bytes(subprocess.check_output(['docker','logs',cid],stderr=subprocess.STDOUT))
t=(O/'time.log').read_text();metric=lambda k:int(re.search(re.escape(k)+r':\s*(\d+)',t)[1])
x=dict(target=cmd,exit_status=rc,wall_seconds=time.monotonic()-start,peak_rss_kib=metric('Maximum resident set size (kbytes)'),swaps=metric('Swaps'),observed_cgroup_peaks=peaks,limits=limits,source_revision='570c0008098b8cc23d16d86f9edb0c2a41b0e118',print_axioms='N/A: OCaml translator rebuild',utc=datetime.datetime.now(datetime.timezone.utc).isoformat(),container_state=json.loads(subprocess.check_output(['docker','inspect',cid]))[0]['State'])
p=H/'aeneas/src/_build/default/main.exe'
if rc==0:x['binary']=dict(path=str(p),bytes=p.stat().st_size,sha256=hashlib.sha256(p.read_bytes()).hexdigest())
(O/'receipt.json').write_text(json.dumps(x,indent=2)+'\n');print(json.dumps(x));sys.exit(rc)
