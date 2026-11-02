"""100 actual fixture-secret pairs through audit copies; complete prover calls, no stubs."""
from pathlib import Path
import asyncio,os,json,hashlib,time
H=Path('/home/dombarker/project-offloads/codex-pv-uc-20261029');O=H/'final-gates/bound/differential';O.mkdir(exist_ok=False)
F=json.loads((H/'fixture-inputs.json').read_text());control=H.parent/'codex-pv-c474-20261029/runtime-private-final/default'
requests={f:json.loads((control/f/'request.json').read_text()) for f in ['transfer','withdrawal']}
B={side:H/'native-target/client'/('pv-uc-'+side+'-audit') for side in ['user','fixture']}
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
pins=json.loads((H/'final-gates/bound/build.json').read_text());assert pins['fixture_unchanged']
assert all(sha(p)==pins['binaries'][p.name]['sha256'] for p in B.values())
slots=asyncio.Semaphore(3);active=set();rows={};start=time.monotonic()
def key(label):
 raw=hashlib.sha256(label.encode()).digest();n=int.from_bytes(raw,'big');out='';alpha='123456789ABCDEFGHJKLMNPQRSTUVWXYZabcdefghijkmnopqrstuvwxyz'
 while n:n,r=divmod(n,58);out=alpha[r]+out
 return '1'*(len(raw)-len(raw.lstrip(b'\0')))+out
async def side(i,side):
 f='transfer' if i%2==0 else 'withdrawal';q=dict(requests[f]);dest=O/f'{i}-{side}';q['proof_dir']=str(dest)
 q['proof_accounts']=[key(f'PV-UC D561 bound differential {i} {j}') for j in range(8)]
 async with slots:
  rfd=None
  if side=='user':
   q.pop('note');q.update(lane_leaf_sets=F['lane_leaf_sets'],withdrawal_amount=250)
   rfd,wfd=os.pipe();os.write(wfd,bytes.fromhex(F['records'][i%2]));os.close(wfd);q['wallet_bytes_fd']=rfd
  p=await asyncio.create_subprocess_exec('taskset','--cpu-list','0-21',str(B[side]),stdin=asyncio.subprocess.PIPE,stdout=asyncio.subprocess.PIPE,stderr=asyncio.subprocess.PIPE,pass_fds=() if rfd is None else (rfd,))
  if rfd is not None:os.close(rfd)
  active.add(p)
  try:out,err=await asyncio.wait_for(p.communicate(json.dumps(q).encode()),180)
  finally:active.discard(p)
  (O/f'{i}-{side}-stdout.json').write_bytes(out);(O/f'{i}-{side}-stderr.txt').write_bytes(err)
  assert p.returncode==0 and not err,(i,side,p.returncode,err.decode())
  return json.loads(out)
def resources():
 c=Path('/sys/fs/cgroup'+Path('/proc/self/cgroup').read_text().split('0::')[1].strip())
 def read(n):return (c/n).read_text().strip()
 return dict(memory_current=read('memory.current'),memory_peak=read('memory.peak'),swap=read('memory.swap.current'),memory_events=read('memory.events'),pids=read('pids.current'),pids_events=read('pids.events'))
async def pair(i):
 u,f=await asyncio.gather(side(i,'user'),side(i,'fixture'))
 files={}
 for name in ['statement.bin','proof-input.bin']:
  a=O/f'{i}-user'/name;b=O/f'{i}-fixture'/name
  assert a.read_bytes()==b.read_bytes(),(i,name,'ENCODING DIFFERENCE: gate failed; never adapt comparator')
  files[name]=dict(sha256=sha(a),bytes=a.stat().st_size,identical=True)
 # Timing is measured separately; mask_audit is the pre-registered removed key.
 assert 'mask_audit' not in u
 f.pop('mask_audit');u.pop('prove_wall_seconds');f.pop('prove_wall_seconds')
 assert u==f,(i,'JSON/instruction difference')
 row=dict(pair=i,fixture='transfer' if i%2==0 else 'withdrawal',files=files,output_and_instructions_identical=True,attempts=u['attempts'])
 rows[i]=row
 (O/f'comparison-{i}.json').write_text(json.dumps(row,indent=2)+'\n')
 if len(rows)%10==0:print('DIFFERENTIAL_PAIRS',len(rows),flush=True)
 (O/'progress.json').write_text(json.dumps(dict(completed=len(rows),required=100,elapsed=time.monotonic()-start,resources=resources()),indent=2)+'\n')
async def review():
 while True:
  await asyncio.sleep(60)
  print('PROGRESS',len(rows),'resources',json.dumps(resources()),flush=True)
async def main():
 tasks=[asyncio.create_task(pair(i)) for i in range(100)];monitor=asyncio.create_task(review())
 try:
  await asyncio.gather(*tasks)
  r=resources();assert r['swap']=='0' and 'oom_kill 0' in r['memory_events'] and r['pids_events']=='max 0',r
  (O/'summary.json').write_text(json.dumps(dict(passed=True,pairs=len(rows),fully_executed_prover_calls=200,elapsed=time.monotonic()-start,resources=r,scope='Finite source-bound deployed-configuration audit copies, one additive input capture; statement, complete compiled proof-input fields, output and instruction bytes equal. No prover stub, no Debug serialization, no random proof-byte equality claim.'),indent=2)+'\n')
 except BaseException as e:
  (O/'failure.json').write_text(json.dumps(dict(error=repr(e),completed=len(rows),resources=resources()),indent=2)+'\n')
  for t in tasks:t.cancel()
  for p in list(active):
   if p.returncode is None:p.terminate()
  await asyncio.gather(*(p.wait() for p in list(active)),return_exceptions=True)
  raise
 finally:monitor.cancel()
asyncio.run(main())
