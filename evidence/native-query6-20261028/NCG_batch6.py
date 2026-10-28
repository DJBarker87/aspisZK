from NCG_host import *
import subprocess,sys,fcntl,os
with (E/'NCG_SERIAL.lock').open('a') as serial:
 fcntl.flock(serial,fcntl.LOCK_EX);admit('NCG_SYNC006')
 s=Path('/tmp/NCG_install.rs').read_text()
 r=py(f"from pathlib import Path;Path({(B+'/NCG_src/crates/aspis-r1-cost-probe/src/NCG_native.rs')!r}).write_text({s!r})");assert r.returncode==0,r.stderr
os.environ['NCG_EXTRA_SOURCES']=json.dumps(['NCG_src/crates/aspis-core/src/field.rs','NCG_src/crates/aspis-core/src/NCG_field_arbitrary.rs'])
# Result controls repaired with exhaustive Error generator, then actual scalar helpers.
rows=['result_unimplied','result_install','result_install_negative']
rows += [t+'_'+c for t in ['row_get','power_get','decoder'] for c in ['callee','callee_negative','caller','caller_negative']]
for n,h in enumerate(rows,46):
 r=subprocess.run([sys.executable,str(E/'NCG_run.py'),f'NCG_K{n:03}',f'NCG_{h}'])
 if r.returncode:raise SystemExit(r.returncode)
 log=(E/f'NCG_K{n:03}'/'stdout.log').read_text()
 if 'could not compile' in log or 'Found 1 compilation errors' in log:raise SystemExit('Own queue stopped on representability/compile error; repair before next shape')
