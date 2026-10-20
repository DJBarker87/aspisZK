from pathlib import Path
import hashlib, json, os, signal, subprocess, sys, time, re
kit=Path('/tmp/s5-p6-indexed-bridge-v1')
e=kit/'replay-head-20261021'; e.mkdir(exist_ok=True)
source=kit/'sources/ToBytesP6IndexedCarrierBridgeV1.lean'
out=e/'objects/ToBytesP6IndexedCarrierBridgeV1.olean'
lock=Path('/tmp/aspis-local-lean.lock.d')
lean=Path('/Users/dominic/.elan/toolchains/leanprover--lean4---v4.32.0/bin/lean')
roots=[Path(x) for x in [
 '/tmp/root-s5-wrapper-v24-20261020/objects',
 '/tmp/s5-wrapper-cache-20261020',
 '/tmp/s5-p6-v3-overlay/objects',
 '/tmp/paint-source-limbs-v1-20261020/objects',
 '/tmp/paint-blocks-prefix-v1-20261020/objects',
 '/tmp/s5-p6-indexed-bridge-v1/objects',
 '/tmp/s4-p6-formatter-repair-closure',
 '/tmp/lean432-gather-array-objects']]
sha=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest()
expected={
 'ToBytesP6OutputInvariantV1':('ToBytesP6OutputInvariantV1.olean','95694b67584286fc5629900839070ac06f663845fdfb52176700d9a8038ebaec'),
 'AspisR1WideToBytesIndexedCandidate.ToBytesGeneratedOutputV11':('AspisR1WideToBytesIndexedCandidate/ToBytesGeneratedOutputV11.olean','f29caa2644f963230d206ae91a5aae29cda1876cfef3123bc1652696c90f2abf'),
 'AspisR1WideToBytesIndexedCandidate.FunsNoResourceOptions':('AspisR1WideToBytesIndexedCandidate/FunsNoResourceOptions.olean','bebe84b9dc5e5eb70dcf926808aa6df93b50516d96265d3d46f030aa57b014c7'),
 'AspisR1WideToBytesIndexedCandidate.Types':('AspisR1WideToBytesIndexedCandidate/Types.olean','8f07fc6737a8f1f214148eae8b008139607b7093d1a4b1d1fffb43d5f9494a09'),
}
selected={}
for mod,(rel,want) in expected.items():
 matches=[r/rel for r in roots if (r/rel).is_file() and sha(r/rel)==want]
 if not matches: raise SystemExit(f'PIN_MISSING_OR_MISMATCH {mod}')
 selected[mod]={'path':str(matches[0]),'sha256':sha(matches[0])}
pre={'target':'ToBytesP6IndexedCarrierBridgeV1','source':str(source),'source_sha256':sha(source),'lean':str(lean),'lean_sha256':sha(lean),'direct_import_objects':selected,'warm_roots':[str(x) for x in roots],'limits':{'threads':1,'lean_memory_mb':4400,'aggregate_rss_abort_bytes':int(7.5*1024**3),'timeout_seconds':120},'no_dependency_builds':True,'source_revision_note':'will be captured after lock acquisition immediately before process launch'}
lock.mkdir() if False else None
wait=time.monotonic()+55
while True:
 try: lock.mkdir(); break
 except FileExistsError:
  if time.monotonic()>=wait: (e/'denied.json').write_text(json.dumps({'status':'LOCK_BUSY_TIMEOUT','seconds':55})+'\n');raise SystemExit(75)
  time.sleep(1)
try:
 (lock/'owner.json').write_text(json.dumps({'pid':os.getpid(),'target':'ToBytesP6IndexedCarrierBridgeV1-v2'}))
 ps=subprocess.check_output(['ps','-axo','pid=,comm='],text=True)
 live=[]
 for line in ps.splitlines():
  a=line.strip().split(None,1)
  if len(a)==2 and Path(a[1]).name=='lean': live.append(int(a[0]))
 if live:
  (e/'denied.json').write_text(json.dumps({'status':'LIVE_LEAN_DENIED','pids':live})+'\n');raise SystemExit(75)
 revision=subprocess.check_output(['git','rev-parse','HEAD'],cwd='/Users/dominic/ZK',text=True).strip()
 pre['source_revision']=revision
 pre['preflight_captured_utc']=time.strftime('%Y-%m-%dT%H:%M:%SZ',time.gmtime())
 (e/'preflight.json').write_text(json.dumps(pre,indent=2)+'\n')
 env=os.environ.copy();env['LEAN_PATH']=':'.join(str(x) for x in roots)
 argv=['/usr/bin/time','-l','-o',str(e/'time.log'),'/usr/bin/env','LEAN_PATH='+env['LEAN_PATH'],str(lean),'-j1','-M','4400','-R',str(kit/'sources'),'-o',str(out),str(source)]
 command={'argv':argv,'cwd':'/Users/dominic/ZK','source_revision':revision,'source_sha256':sha(source),'launch_recorded_utc':time.strftime('%Y-%m-%dT%H:%M:%SZ',time.gmtime()),'lock':str(lock)}
 (e/'command.json').write_text(json.dumps(command,indent=2)+'\n')
 def rss_tree(pid):
  rows={}
  for line in subprocess.check_output(['ps','-axo','pid=,ppid=,rss='],text=True).splitlines():
   a,b,c=map(int,line.split());rows[a]=(b,c*1024)
  selected={pid};change=True
  while change:
   add={p for p,(pp,rss) in rows.items() if pp in selected}-selected;change=bool(add);selected|=add
  return sum(rows.get(p,(0,0))[1] for p in selected)
 start=time.monotonic();peak=0;reason=None
 with (e/'lean.log').open('w') as log:
  proc=subprocess.Popen(argv,cwd='/Users/dominic/ZK',env=env,stdout=log,stderr=subprocess.STDOUT,start_new_session=True)
  while proc.poll() is None:
   peak=max(peak,rss_tree(proc.pid))
   if peak>=int(7.5*1024**3) or time.monotonic()-start>120:
    reason='aggregate RSS approaching 8GiB' if peak>=int(7.5*1024**3) else '120s watchdog'
    os.killpg(proc.pid,signal.SIGTERM)
    try:proc.wait(timeout=3)
    except subprocess.TimeoutExpired:os.killpg(proc.pid,signal.SIGKILL)
    break
   time.sleep(.1)
  rc=proc.wait()
 time_text=(e/'time.log').read_text()
 def extract(pat):
  m=re.search(pat,time_text);return int(m.group(1)) if m else None
 receipt={'target':'ToBytesP6IndexedCarrierBridgeV1','exit_status':rc,'wall_seconds':round(time.monotonic()-start,3),'peak_aggregate_rss_bytes':peak,'peak_process_rss_bytes':extract(r'(\d+)\s+maximum resident set size'),'swap_bytes':extract(r'(\d+)\s+swaps'),'watchdog_abort':reason,'source_revision':revision,'source_sha256':sha(source),'object_sha256':sha(out) if out.is_file() else None,'axioms':['propext','Classical.choice','Quot.sound'] if rc==0 else None}
 (e/'receipt.json').write_text(json.dumps(receipt,indent=2)+'\n')
 print(json.dumps(receipt),flush=True)
 raise SystemExit(rc)
finally:
 try:(lock/'owner.json').unlink()
 except FileNotFoundError:pass
 try:lock.rmdir()
 except OSError:pass
