from NCG_host import *
import subprocess,sys,fcntl,os
with (E/'NCG_SERIAL.lock').open('a') as serial:
 fcntl.flock(serial,fcntl.LOCK_EX);admit('NCG_SYNC008')
 s=Path('/tmp/NCG_tail.rs').read_text();marker='\n#[cfg(kani)] #[path="'+B+'/NCG_src/crates/aspis-r1-cost-probe/src/NCG_tail.rs"] mod NCG_tail;\n'
 r=py(f"from pathlib import Path;p=Path({(B+'/NCG_src/crates/aspis-r1-cost-probe/src/fast_pairing.rs')!r});s=p.read_text();needle='\\n}}\\n\\n\\nuse aspis_core::field::';assert s.count(needle)==1;marker={marker!r};p.write_text(s if marker in s else s.replace(needle,marker+needle));(p.parent/'NCG_tail.rs').write_text({s!r})");assert r.returncode==0,r.stderr
os.environ['NCG_EXTRA_SOURCES']=json.dumps(['NCG_src/crates/aspis-core/src/field.rs','NCG_src/crates/aspis-core/src/NCG_field_arbitrary.rs','NCG_src/crates/aspis-r1-cost-probe/src/fast_pairing.rs','NCG_src/crates/aspis-r1-cost-probe/src/NCG_tail.rs'])
for n,h in enumerate([f'NCG_tail_{mode}'+suffix for mode in range(3) for suffix in ['','_negative']],72):
 r=subprocess.run([sys.executable,str(E/'NCG_run.py'),f'NCG_K{n:03}','fast_pairing::canonical::NCG_tail::'+h])
 if r.returncode:raise SystemExit(r.returncode)
 log=(E/f'NCG_K{n:03}'/'stdout.log').read_text()
 if 'could not compile' in log or 'timed out' in log:raise SystemExit('Own tail source needs repair or smaller split')
