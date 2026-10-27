"""Retain exact per-attempt scratch sources as patches, not shipped files."""
from pathlib import Path
import subprocess
E=Path(__file__).resolve().parent;H='dombarker@100.108.41.90';B='/home/dombarker/project-offloads/codex-cx-leaf-p6-5-20261027'
code='''from pathlib import Path
import difflib
B=Path("'''+B+'''");root='crates/aspis-r1-cost-probe/src/'
for attempt in sorted(B.glob('LPe_K[0-9][0-9][0-9]')):
 parts=[]
 for f in ['lib.rs','fast_pairing.rs','verifier.rs','LPe_replay.rs','LPe_verifier.rs']:
  snap=attempt/'sources'/'LPe_src'/root/f
  if not snap.exists():continue
  old='' if f.startswith('LPe_') else (B/('LPe_frozen_'+f)).read_text()
  parts.append(''.join(difflib.unified_diff(old.splitlines(True),snap.read_text().splitlines(True),fromfile='/dev/null' if f.startswith('LPe_') else 'a/'+root+f,tofile='b/'+root+f)))
 (attempt/'LPe_harness.patch').write_text(''.join(parts))
'''
r=subprocess.run(['ssh',H,'python3','-'],input=code,text=True,capture_output=True);assert r.returncode==0,r.stderr
for i in range(1,21):
 a=f'LPe_K{i:03}';subprocess.run(['scp','-q',H+':'+B+'/'+a+'/LPe_harness.patch',str(E/a/'LPe_harness.patch')],check=True)
