from NCG_host import *
import subprocess,sys,fcntl,os
# New pointer/allocator use is admitted only if all exact Result<Vec<[u64;4]>,Error> shape controls ran.
for n in [39,42,43]:
 p=E/f'NCG_K{n:03}'/'stdout.log';assert p.exists() and 'VERIFICATION:- FAILED' in p.read_text() and 'could not compile' not in p.read_text(),'No allocator contract reliance without shape controls'
assert 'VERIFICATION:- SUCCESSFUL' in (E/'NCG_K041/stdout.log').read_text()
with (E/'NCG_SERIAL.lock').open('a') as serial:
 fcntl.flock(serial,fcntl.LOCK_EX);admit('NCG_SYNC009')
 s=Path('/tmp/NCG_final.rs').read_text()
 r=py(f"from pathlib import Path;Path({(B+'/NCG_src/crates/aspis-r1-cost-probe/src/NCG_native.rs')!r}).write_text({s!r})");assert r.returncode==0,r.stderr
os.environ['NCG_EXTRA_SOURCES']=json.dumps(['NCG_src/crates/aspis-core/src/field.rs','NCG_src/crates/aspis-core/src/NCG_field_arbitrary.rs','NCG_src/crates/aspis-r1-cost-probe/src/fast_pairing.rs','NCG_src/crates/aspis-r1-cost-probe/src/NCG_tail.rs'])
for n,h in enumerate(['reserve_callee','reserve_callee_negative','reserve_caller','reserve_caller_negative'],77):
 r=subprocess.run([sys.executable,str(E/'NCG_run.py'),f'NCG_K{n:03}',f'NCG_{h}'])
 if r.returncode:raise SystemExit(r.returncode)
 log=(E/f'NCG_K{n:03}'/'stdout.log').read_text()
 if 'could not compile' in log or 'timed out' in log:raise SystemExit('Own allocator queue stopped for split/repair')
