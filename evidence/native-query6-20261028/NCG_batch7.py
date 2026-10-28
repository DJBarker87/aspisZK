from NCG_host import *
import subprocess,sys,fcntl,os
with (E/'NCG_SERIAL.lock').open('a') as serial:
 fcntl.flock(serial,fcntl.LOCK_EX);admit('NCG_SYNC007')
 s=Path('/tmp/NCG_coefficients.rs').read_text()
 r=py(f"from pathlib import Path;Path({(B+'/NCG_src/crates/aspis-r1-cost-probe/src/NCG_native.rs')!r}).write_text({s!r})");assert r.returncode==0,r.stderr
os.environ['NCG_EXTRA_SOURCES']=json.dumps(['NCG_src/crates/aspis-core/src/field.rs','NCG_src/crates/aspis-core/src/NCG_field_arbitrary.rs'])
for n,h in enumerate([t+c for t in ['scale',*[f'coefficient{i}' for i in range(4)]] for c in ['','_negative']],62):
 r=subprocess.run([sys.executable,str(E/'NCG_run.py'),f'NCG_K{n:03}',f'NCG_{h}'])
 if r.returncode:raise SystemExit(r.returncode)
 log=(E/f'NCG_K{n:03}'/'stdout.log').read_text()
 if 'could not compile' in log:raise SystemExit('Own source repair required')
 if 'timed out' in log:
  (E/'NCG_HOLD').write_text('Coefficient shape needs a smaller split before its control.\n')
  raise SystemExit('Own adaptive queue stopped on timeout')
