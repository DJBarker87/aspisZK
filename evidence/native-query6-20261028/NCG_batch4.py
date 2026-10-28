from NCG_host import *
import subprocess,sys,fcntl
with (E/'NCG_SERIAL.lock').open('a') as serial:
 fcntl.flock(serial,fcntl.LOCK_EX);admit('NCG_SYNC004')
 s=Path('/tmp/NCG_fold_logs.rs').read_text()
 r=py(f"from pathlib import Path;Path({(B+'/NCG_src/crates/aspis-r1-cost-probe/src/NCG_native.rs')!r}).write_text({s!r})");assert r.returncode==0,r.stderr
for n,h in enumerate(['circle','circle_negative','line','line_negative'],18):
 r=subprocess.run([sys.executable,str(E/'NCG_run.py'),f'NCG_K{n:03}',f'NCG_{h}'])
 if r.returncode:raise SystemExit(r.returncode)
