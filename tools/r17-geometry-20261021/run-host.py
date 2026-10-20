#!/usr/bin/env python3
"""Run inside the capped host scope; keep compilation and execution separate."""
import hashlib,json,pathlib,subprocess,time,os
root=pathlib.Path(__file__).resolve().parents[2]
out=root/'receipts';out.mkdir(exist_ok=True)
commands=[['/home/dombarker/.cargo/bin/cargo','test','--release','-j','4','--manifest-path',str(root/'tools/r17-geometry-20261021/Cargo.toml'),'--','--nocapture','--test-threads=1']]
for attempt,cmd in enumerate(commands,1):
 start=time.monotonic()
 with (out/f'output-{attempt}.log').open('w') as f:
  result=subprocess.run(['/usr/bin/time','-v','-o',str(out/f'time-{attempt}.log'),*cmd],cwd=root,stdout=f,stderr=subprocess.STDOUT)
 receipt={'attempt':attempt,'target':'R17 optimized native executable certificate','command':cmd,'exit':result.returncode,'wall_seconds':time.monotonic()-start,'axioms':'N/A: executable Rust certificate','source_revision':os.environ['R17_REVISION'],'expected_work':'compilation then named tests: closed-form entries, native geometry, transports; no dense elimination','scope':{'MemoryHigh':'6G','MemoryMax':'8G','MemorySwapMax':0,'TasksMax':64},'time_log':(out/f'time-{attempt}.log').read_text(),'source_pins':{str(p.relative_to(root)):hashlib.sha256(p.read_bytes()).hexdigest() for p in [root/'tools/r17-geometry-20261021/src/lib.rs',root/'crates/aspis-r1-cost-probe/src/fast_domain.rs',root/'crates/aspis-r1-cost-probe/src/transport.rs']}}
 binaries=list((root/'tools/r17-geometry-20261021/target/release/deps').glob('r17_geometry_certificate-*'))
 receipt['binaries']=[{'name':p.name,'sha256':hashlib.sha256(p.read_bytes()).hexdigest(),'bytes':p.stat().st_size} for p in binaries if p.is_file() and os.access(p,os.X_OK)]
 (out/f'receipt-{attempt}.json').write_text(json.dumps(receipt,indent=2)+'\n')
 print(json.dumps(receipt,indent=2));print((out/f'output-{attempt}.log').read_text())
 raise SystemExit(result.returncode)
