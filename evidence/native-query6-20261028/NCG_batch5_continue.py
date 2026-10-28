from NCG_host import *
import subprocess,sys,os
os.environ['NCG_EXTRA_SOURCES']=json.dumps(['NCG_src/crates/aspis-core/src/field.rs','NCG_src/crates/aspis-core/src/NCG_field_arbitrary.rs'])
rows=[(35,'slice_frame_wrong')]+list(enumerate(['vec_'+c for c in ['contract','wrong','weak_contract','real','unimplied','frame_wrong','install','install_negative']],38))
for n,h in rows:
 r=subprocess.run([sys.executable,str(E/'NCG_run.py'),f'NCG_K{n:03}',f'NCG_{h}'])
 if r.returncode:raise SystemExit(r.returncode)
 log=(E/f'NCG_K{n:03}'/'stdout.log').read_text()
 if 'could not compile' in log or 'timed out' in log:raise SystemExit('New independent shape requires repair/split; queued repetitions stopped')
