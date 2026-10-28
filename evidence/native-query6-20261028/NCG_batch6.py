from NCG_host import *
import subprocess,sys,fcntl,os
with (E/'NCG_SERIAL.lock').open('a') as serial:
 fcntl.flock(serial,fcntl.LOCK_EX);admit('NCG_SYNC006_REPAIR')
 s=Path('/tmp/NCG_install_actual.rs').read_text()
 r=py(f"from pathlib import Path;Path({(B+'/NCG_src/crates/aspis-r1-cost-probe/src/NCG_native.rs')!r}).write_text({s!r})");assert r.returncode==0,r.stderr
os.environ['NCG_EXTRA_SOURCES']=json.dumps(['NCG_src/crates/aspis-core/src/field.rs','NCG_src/crates/aspis-core/src/NCG_field_arbitrary.rs'])
# Install a Kani-only contract directly on the frozen field decoder, retaining its body.
def annotate(invert,tag):
 admit(tag)
 annotation=(E/'NCG_decoder_annotation.txt').read_text()
 if invert:annotation=annotation.replace('>|match r', '>|!match r')
 original=(E/'NCG_decoder_annotation.txt').read_text()
 r=py(f"from pathlib import Path;p=Path({(B+'/NCG_src/crates/aspis-core/src/field.rs')!r});s=p.read_text();needle='pub fn from_le_bytes(bytes: [u8; 4]) -> Option<M31> {{';normal={original!r};bad=normal.replace('>|match r','>|!match r');s=s.replace(normal+needle,needle).replace(bad+needle,needle);assert s.count(needle)==1;s=s.replace(needle,{annotation!r}+needle);p.write_text(s)");assert r.returncode==0,r.stderr
annotate(False,'NCG_ANNOTATE_INITIAL')
# Result controls repaired with exhaustive Error generator, then actual scalar helpers.
rows=['result_wrong','result_frame_wrong','result_unimplied']
rows += [t+'_'+c for t in ['row_get','power_get'] for c in ['callee','callee_negative','caller','caller_negative']]
for n,h in enumerate(rows,47):
 r=subprocess.run([sys.executable,str(E/'NCG_run.py'),f'NCG_K{n:03}',f'NCG_{h}'])
 if r.returncode:raise SystemExit(r.returncode)
 log=(E/f'NCG_K{n:03}'/'stdout.log').read_text()
 if 'could not compile' in log or 'Found 1 compilation errors' in log:raise SystemExit('Own queue stopped on representability/compile error; repair before next shape')

for n,h,invert in [(58,'actual_decoder_contract',False),(59,'actual_decoder_contract',True),(60,'actual_base_decoder',False),(61,'actual_base_decoder_negative',False)]:
 annotate(invert,f'NCG_ANNOTATE{n:03}')
 r=subprocess.run([sys.executable,str(E/'NCG_run.py'),f'NCG_K{n:03}',f'NCG_{h}'])
 if r.returncode:raise SystemExit(r.returncode)
 log=(E/f'NCG_K{n:03}'/'stdout.log').read_text()
 if 'could not compile' in log:raise SystemExit('Own actual contract repair required')
