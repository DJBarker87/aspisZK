from pathlib import Path
import difflib,subprocess,json
E=Path(__file__).resolve().parent
for directory in sorted(E.glob('NDG_*')):
 if not directory.is_dir() or not (directory/'receipt.json').exists():continue
 sources=directory/'sources/NDG_src'
 if not sources.exists():continue
 patch=[]
 for p in sorted(sources.rglob('*')):
  if not p.is_file():continue
  n=str(p.relative_to(sources));r=subprocess.run(['git','show','4bb3b3f5:'+n],capture_output=True,text=True)
  b=r.stdout if r.returncode==0 else '';s=p.read_text()
  patch.append(''.join(difflib.unified_diff(b.splitlines(True),s.splitlines(True),fromfile='a/'+n if b else '/dev/null',tofile='b/'+n)))
 q=directory/'NDG_harness.patch'
 if q.exists():assert q.read_text()==''.join(patch)
 else:q.write_text(''.join(patch))
 for p in sorted(sources.rglob('*'),reverse=True):
  if p.is_file():p.unlink()
  elif p.is_dir():p.rmdir()
 sources.rmdir()
print('scratch Rust represented by patches; original source hashes remain in receipts')
