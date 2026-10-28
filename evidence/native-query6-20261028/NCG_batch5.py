from NCG_host import *
import subprocess,sys,fcntl
with (E/'NCG_SERIAL.lock').open('a') as serial:
 fcntl.flock(serial,fcntl.LOCK_EX);admit('NCG_SYNC005')
 s=Path('/tmp/NCG_shapes.rs').read_text()
 r=py(f"from pathlib import Path;Path({(B+'/NCG_src/crates/aspis-r1-cost-probe/src/NCG_native.rs')!r}).write_text({s!r})");assert r.returncode==0,r.stderr
 core=(E/'NCG_field_arbitrary.rs.txt').read_text()
 marker='\n#[cfg(kani)] #[path="NCG_field_arbitrary.rs"] mod NCG_field_arbitrary;\n'
 r=py(f"from pathlib import Path;p=Path({(B+'/NCG_src/crates/aspis-core/src/field.rs')!r});s=p.read_text();marker={marker!r};p.write_text(s if marker in s else s+marker);(p.parent/'NCG_field_arbitrary.rs').write_text({core!r})");assert r.returncode==0,r.stderr
import os
os.environ['NCG_EXTRA_SOURCES']=json.dumps(['NCG_src/crates/aspis-core/src/field.rs','NCG_src/crates/aspis-core/src/NCG_field_arbitrary.rs'])
for n,h in enumerate([t+'_'+c for t in ['option','slice','vec'] for c in ['contract','wrong','weak_contract','real','unimplied','frame_wrong','install','install_negative']],22):
 r=subprocess.run([sys.executable,str(E/'NCG_run.py'),f'NCG_K{n:03}',f'NCG_{h}'])
 if r.returncode:raise SystemExit(r.returncode)
 log=(E/f'NCG_K{n:03}'/'stdout.log').read_text()
 if 'could not compile' in log or 'Found 1 compilation errors' in log:raise SystemExit('Own queue stopped on representability/compile error; repair before next shape')
