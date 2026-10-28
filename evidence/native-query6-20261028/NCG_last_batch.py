from NCG_host import *
import subprocess,sys,fcntl,os
with (E/'NCG_SERIAL.lock').open('a') as serial:
 fcntl.flock(serial,fcntl.LOCK_EX);admit('NCG_SYNC010')
 s=Path('/tmp/NCG_tail_finish.rs').read_text();n=Path('/tmp/NCG_last_native.rs').read_text()
 r=py(f"from pathlib import Path;p=Path({(B+'/NCG_src/crates/aspis-r1-cost-probe/src')!r});(p/'NCG_tail.rs').write_text({s!r});(p/'NCG_native.rs').write_text({n!r})");assert r.returncode==0,r.stderr
os.environ['NCG_EXTRA_SOURCES']=json.dumps(['NCG_src/crates/aspis-core/src/field.rs','NCG_src/crates/aspis-core/src/NCG_field_arbitrary.rs','NCG_src/crates/aspis-r1-cost-probe/src/fast_pairing.rs','NCG_src/crates/aspis-r1-cost-probe/src/NCG_tail.rs'])
rows=['fast_pairing::canonical::NCG_tail::NCG_'+t+s for t in ['finish','finish_add','three_push'] for s in ['','_negative']]
rows+=['verifier::candidate::NCG_native::NCG_log_index','verifier::candidate::NCG_native::NCG_log_index_negative']
for n,h in enumerate(rows,78):
 r=subprocess.run([sys.executable,str(E/'NCG_run.py'),f'NCG_K{n:03}',h])
 if r.returncode:raise SystemExit(r.returncode)
 log=(E/f'NCG_K{n:03}'/'stdout.log').read_text()
 if 'could not compile' in log or 'timed out' in log:raise SystemExit('Own final queue stopped: split/repair before any repetition')
