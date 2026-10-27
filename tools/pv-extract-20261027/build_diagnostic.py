from pathlib import Path
import json,subprocess,runpy,time,hashlib
D=Path('/home/dombarker/project-offloads/codex-pv-extract-20261027'); O=D/'build-diagnostic-001';O.mkdir()
scanner=runpy.run_path('/home/dombarker/project-offloads/codex-cx-prover-rw-20261023/native-entropy/reservation.py')
a=scanner['admission']();(O/'admission-before.json').write_text(json.dumps(a,indent=2));assert a['allowed'],a.get('reason')
image='sha256:ef96e46342a4159b6a62663e1ff5474a5f5deaf260daf08ea7b0963974418db7'
cmd=['docker','create','--name','pv-extract-diagnostic-001','--network','none','--memory','8g','--memory-swap','8g','--pids-limit','64','--cpus','4','--user','0','--mount',f'type=bind,src={D}/pipeline,dst=/job','--mount',f'type=bind,src={O},dst=/receipt','--entrypoint','/bin/bash',image,'-c','while [ ! -f /receipt/go ]; do sleep 0.1; done; exec /usr/bin/time -v -o /receipt/time.log opam exec -- bash /job/build-base.sh']
(O/'target.json').write_text(json.dumps(dict(target=cmd,phase='optimized OCaml compilation of copied Charon/Aeneas; no arithmetic gate',revision='7599dff5b274d52324ae8681664f6b343f9a81ac',print_axioms='N/A OCaml compilation'),indent=2))
cid=subprocess.check_output(cmd,text=True).strip();subprocess.run(['docker','start',cid],check=True,stdout=subprocess.DEVNULL)
pid=json.loads(subprocess.check_output(['docker','inspect',cid]))[0]['State']['Pid'];cg=Path('/sys/fs/cgroup'+Path(f'/proc/{pid}/cgroup').read_text().split('0::')[1].strip())
subprocess.run(['sudo','-n','tee',str(cg/'memory.high')],input=str(6*2**30),text=True,check=True,stdout=subprocess.DEVNULL)
release=runpy.run_path('/home/dombarker/project-offloads/codex-cx-prover-rw-20261023/native-entropy/docker_gate.py')['release']
try:limits=release(cg,O,scanner['admission'])
except BaseException:
 subprocess.run(['docker','stop','--time','1',cid]);raise
start=time.monotonic(); w=subprocess.Popen(['docker','wait',cid],stdout=subprocess.PIPE,text=True);peaks={}
while w.poll() is None:
 for k in ['memory.peak','memory.swap.peak']:
  try:peaks[k]=max(peaks.get(k,0),int((cg/k).read_text()))
  except FileNotFoundError:pass
 time.sleep(.2)
status=int(w.communicate()[0]);(O/'output.log').write_bytes(subprocess.check_output(['docker','logs',cid],stderr=subprocess.STDOUT));(O/'receipt.json').write_text(json.dumps(dict(exit=status,wall_seconds=time.monotonic()-start,limits=limits,peaks=peaks,print_axioms='N/A',time_log=(O/'time.log').read_text()),indent=2));print(status)
