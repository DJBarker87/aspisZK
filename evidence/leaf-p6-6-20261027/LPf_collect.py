"""Preserve exact per-attempt scratch source changes as patches, never binaries."""
from pathlib import Path
import subprocess,json,difflib
E=Path(__file__).resolve().parent;B='/home/dombarker/project-offloads/codex-cx-leaf-p6-6-20261027';H='dombarker@100.108.41.90';F='4bb3b3f51e16b4525f1d10336e2b0bcbbd775387'
for p in sorted(E.glob('LPf_K*/receipt.json')):
 dst=p.parent/'LPf_harness.patch'
 if dst.exists():continue
 r=json.loads(p.read_text());out=[]
 for f in r['sources']:
  if not f.startswith('LPf_src/') or f.endswith('Cargo.lock'):continue
  path=f[len('LPf_src/'):]
  new=subprocess.run(['ssh',H,'cat '+B+'/'+p.parent.name+'/sources/'+f],capture_output=True,text=True,check=True).stdout
  old=subprocess.run(['git','show',F+':'+path],capture_output=True,text=True)
  out.append(''.join(difflib.unified_diff(old.stdout.splitlines(True),new.splitlines(True),fromfile='a/'+path if old.returncode==0 else '/dev/null',tofile='b/'+path,n=0)))
 dst.write_text(''.join(out))
