"""100 actual fixture-secret pairs through audit copies; complete prover calls, no stubs."""
from pathlib import Path
import asyncio,os,json,hashlib,time
H=Path('/home/dombarker/project-offloads/codex-pv-uc-20261029');O=H/'final-gates/uc5/differential-final';O.mkdir(exist_ok=False)
F=json.loads((H/'fixture-inputs.json').read_text());control=H.parent/'codex-pv-c474-20261029/runtime-private-final/default'
requests={f:json.loads((control/f/'request.json').read_text()) for f in ['transfer','withdrawal']}
B={'user':H/'native-target/client/user_client','fixture':H/'native-target/client/devnet_spend'}
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
pins=json.loads((H/'final-gates/uc5-final/build.json').read_text());assert pins['fixture_unchanged']
assert all(sha(p)==pins['binaries'][p.name]['sha256'] for p in B.values())
print('EXPECTED WORK: optimized proof generation in 200 final-production/fixture prover calls; no compilation or timing experiment',flush=True)
slots=asyncio.Semaphore(3);active=set();rows={};start=time.monotonic()
def key(label):
 raw=hashlib.sha256(label.encode()).digest();n=int.from_bytes(raw,'big');out='';alpha='123456789ABCDEFGHJKLMNPQRSTUVWXYZabcdefghijkmnopqrstuvwxyz'
 while n:n,r=divmod(n,58);out=alpha[r]+out
 return '1'*(len(raw)-len(raw.lstrip(b'\0')))+out
async def side(i,side):
 f='transfer' if i%2==0 else 'withdrawal';q=dict(requests[f]);dest=O/f'{i}-{side}';q['proof_dir']=str(dest)
 q['proof_accounts']=[key(f'PV-UC D577 alias-safe final production differential {i} {j}') for j in range(8)]
 async with slots:
  rfd=None; output_read=None; output_write=None
  if side=='user':
   q.pop('note');q.update(lane_leaf_sets=F['lane_leaf_sets'],withdrawal_amount=250)
   rfd,wfd=os.pipe();os.write(wfd,bytes.fromhex(F['records'][i%2]));os.close(wfd);q['wallet_bytes_fd']=rfd
   output_read,output_write=os.pipe();q['wallet_output_fd']=output_write
  p=await asyncio.create_subprocess_exec('taskset','--cpu-list','0-21',str(B[side]),stdin=asyncio.subprocess.PIPE,stdout=asyncio.subprocess.PIPE,stderr=asyncio.subprocess.PIPE,pass_fds=() if rfd is None else (rfd,output_write))
  if rfd is not None:os.close(rfd);os.close(output_write)
  active.add(p)
  try:out,err=await asyncio.wait_for(p.communicate(json.dumps(q).encode()),180)
  finally:
   if p.returncode is not None:active.discard(p)
  if output_read is not None:
   custody=os.read(output_read,213);os.close(output_read)
   assert custody==bytes.fromhex(F['records'][i%2]),(i,'custody record mismatch')
  (O/f'{i}-{side}-stdout.json').write_bytes(out if side=='user' else json.dumps({k:v for k,v in json.loads(out).items() if k!='mask_audit'}).encode());(O/f'{i}-{side}-stderr.txt').write_bytes(err)
  assert p.returncode==0 and not err,(i,side,p.returncode,err.decode())
  return json.loads(out)
def resources():
 c=Path('/sys/fs/cgroup'+Path('/proc/self/cgroup').read_text().split('0::')[1].strip())
 def read(n):return (c/n).read_text().strip()
 return dict(memory_current=read('memory.current'),memory_peak=read('memory.peak'),swap=read('memory.swap.current'),memory_events=read('memory.events'),pids=read('pids.current'),pids_events=read('pids.events'))
async def pair(i):
 u,f=await asyncio.gather(side(i,'user'),side(i,'fixture'))
 files={}
 for name in ['statement.bin']:
  a=O/f'{i}-user'/name;b=O/f'{i}-fixture'/name
  assert a.read_bytes()==b.read_bytes(),(i,name,'ENCODING DIFFERENCE: gate failed; never adapt comparator')
  files[name]=dict(sha256=sha(a),bytes=a.stat().st_size,identical=True)
 # Timing is measured separately; mask_audit is the pre-registered removed key.
 assert 'mask_audit' not in u
 f.pop('mask_audit');u.pop('prove_wall_seconds');f.pop('prove_wall_seconds')
 assert u==f,(i,'JSON/instruction difference')
 # Search every generated user file, stdout and stderr against each complete
 # secret field, plus the complete 212-byte record. No secret needles are logged.
 record=bytes.fromhex(F['records'][i%2])
 widths=[('input_key',0,32),('input_salt',32,32),('input_value',64,8),('asset',72,4),('change_key',76,32),('change_salt',108,32),('recipient_owner',140,32),('recipient_salt',172,32),('recipient_value',204,8),('record',0,212)]
 targets=[*sorted((O/f'{i}-user').rglob('*')),O/f'{i}-user-stdout.json',O/f'{i}-user-stderr.txt']
 hits=[];scanned=[]
 for path in targets:
  if not path.is_file():continue
  raw=path.read_bytes();scanned.append(dict(path=str(path.relative_to(O)),bytes=len(raw),sha256=sha(path)))
  for label,field_offset,width in widths:
   needle=record[field_offset:field_offset+width];offset=raw.find(needle)
   if offset>=0:hits.append(dict(path=str(path.relative_to(O)),field=label,width=width,offset=offset))
 assert not (O/f'{i}-user/wallet-recovery.bin').exists()
 # Record literal byte matches, including incidental/public-value matches,
 # without suppressing or reclassifying them into a passing literal gate.
 scan=dict(evidence_class='finite exact-byte search; full-width raw fields and record; not noninterference',scanned=scanned,hits=hits,raw_pipe_record_matches=True,literal_full_field_gate_pass=not hits,key_salt_record_gate_pass=not any(h['width']>=32 for h in hits))
 (O/f'secret-scan-{i}.json').write_text(json.dumps(scan,indent=2)+'\n')
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
  scans=[json.loads((O/f'secret-scan-{i}.json').read_text()) for i in range(100)]
  (O/'secret-scan-summary.json').write_text(json.dumps(dict(evidence_class='finite full-width raw-field exact-byte search over every user output',pairs=100,files=sum(len(s['scanned']) for s in scans),literal_full_field_gate_pass=all(s['literal_full_field_gate_pass'] for s in scans),key_salt_record_gate_pass=all(s['key_salt_record_gate_pass'] for s in scans),hits=[dict(pair=i,**h) for i,s in enumerate(scans) for h in s['hits']]),indent=2)+'\n')
  (O/'summary.json').write_text(json.dumps(dict(passed=True,pairs=len(rows),fully_executed_prover_calls=200,elapsed=time.monotonic()-start,resources=r,scope='Finite final production client versus unchanged fixture executable; public statement bytes, JSON and instruction bytes equal; custody record checked only in pipe memory. No proof-input file capture, no random proof-byte equality claim.'),indent=2)+'\n')
 except BaseException as e:
  (O/'failure.json').write_text(json.dumps(dict(error=repr(e),completed=len(rows),resources=resources()),indent=2)+'\n')
  for t in tasks:t.cancel()
  for p in list(active):
   if p.returncode is None:p.terminate()
  await asyncio.gather(*(p.wait() for p in list(active)),return_exceptions=True)
  raise
 finally:monitor.cancel()
asyncio.run(main())
