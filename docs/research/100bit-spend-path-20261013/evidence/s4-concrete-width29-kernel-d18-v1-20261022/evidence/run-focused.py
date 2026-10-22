import json, os, pathlib, subprocess, time, hashlib, sys
root=pathlib.Path('/Users/dominic/ZK')
base=json.loads((root/'/tmp/d18-s4-width29-literal-join-v1/evidence/preflight.json').read_text())['lean_path']
prefix=[
 '/tmp/d18-s4-width29-literal-join-v4/objects',
 '/tmp/root-s4-concrete-kernel-ops-v1-20261021/objects',
 '/Users/dominic/ZK/docs/research/100bit-spend-path-20261013/lean-candidates/s4-head-codec-projection-v1-20261021/v2-fin26-attempt2/objects',
 '/Users/dominic/ZK/docs/research/100bit-spend-path-20261013/lean-candidates/s4-head-codec-projection-v1-20261021/c1-exact-name-receipt-v1/objects',
 '/Users/dominic/ZK/docs/research/100bit-spend-path-20261013/lean-candidates/s4-head-codec-projection-v1-20261021',
 '/tmp/root-s4-tail-coefficient-powers-v1-20261022/objects',
 '/tmp/root-s4-first-fold-opening-geometry-v1-20261022/objects',
 '/tmp/s4-tail-slot-embedding-v1/attempt7/objects',
 '/tmp/s4-tail-slot-byte-projections-v1/attempt6/objects',
 '/tmp/s4-tail-parser-embedding-v1/attempt5/objects',
 '/tmp/s4-tail-parser-embedding-v1/attempt15/objects',
 '/tmp/root-s4-tail-trace-member-witness-v1-20261022/objects',
 '/tmp/root-s4-callback-parser-v2-20261021/objects',
]
for p in prefix:
 if not pathlib.Path(p).is_dir(): raise SystemExit('missing import root '+p)
path=':'.join(prefix+[base])
work=pathlib.Path('/tmp/d18-s4-concrete-width29-kernel-v1'); (work/'sources').mkdir(parents=True,exist_ok=True); (work/'objects').mkdir(exist_ok=True); (work/'evidence').mkdir(exist_ok=True)
src=pathlib.Path('/tmp/D18S4ConcreteWidth29KernelV1.lean'); dest=work/'sources'/src.name; dest.write_bytes(src.read_bytes())
lock=pathlib.Path('/tmp/aspis-local-lean.lock.d')
end=time.monotonic()+55
while True:
 try: lock.mkdir(); break
 except FileExistsError:
  if time.monotonic()>=end: raise SystemExit('LOCK_BUSY_TIMEOUT')
  time.sleep(.25)
try:
 procs=subprocess.check_output(['ps','-axo','pid=,comm='],text=True)
 active=[]
 for line in procs.splitlines():
  parts=line.strip().split(None,1)
  if len(parts)==2 and pathlib.Path(parts[1]).name=='lean': active.append(int(parts[0]))
 if active: raise SystemExit('LIVE_LEAN '+repr(active))
 owner={'target':dest.stem,'pid':os.getpid(),'source_sha256':hashlib.sha256(dest.read_bytes()).hexdigest(),'lean_path_sha256':hashlib.sha256(path.encode()).hexdigest(),'created':time.time()}
 (lock/'owner.json').write_text(json.dumps(owner,indent=2))
 env=os.environ.copy(); env['LEAN_PATH']=path
 cmd=['/usr/bin/time','-l','-o',str(work/'evidence/time.log'),'/Users/dominic/.elan/toolchains/leanprover--lean4---v4.32.0/bin/lean','-j1','-M4400','-R',str(work/'sources'),'-o',str(work/'objects'/(dest.stem+'.olean')),str(dest)]
 (work/'evidence/LEAN_PATH.txt').write_text(path)
 (work/'evidence/command.json').write_text(json.dumps({'argv':cmd,'cwd':os.getcwd(),'source_sha256':owner['source_sha256'],'lean_path_sha256':owner['lean_path_sha256']},indent=2))
 t=time.monotonic(); p=subprocess.run(cmd,env=env); elapsed=time.monotonic()-t
 (work/'evidence/receipt.json').write_text(json.dumps({'target':dest.stem,'exit_status':p.returncode,'wall_seconds':elapsed,'source_sha256':owner['source_sha256'],'lean_path_sha256':owner['lean_path_sha256']},indent=2))
 print('EXIT',p.returncode,'SECONDS',round(elapsed,3))
finally:
 try: (lock/'owner.json').unlink()
 except FileNotFoundError: pass
 try: lock.rmdir()
 except OSError: pass
