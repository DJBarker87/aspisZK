"""Own evidence hygiene and deterministic source patch; no proof launch."""
from pathlib import Path
import json,hashlib,lzma,subprocess,difflib
E=Path(__file__).resolve().parent
sha=lambda b:hashlib.sha256(b).hexdigest()
rs={}
for task in json.loads((E/'PCG_TASKS.json').read_text()).values():
 for n,p in task.get('files',{}).items():
  if n.startswith('PCG_src/') and (E/p).is_file():rs[n[8:]]=(E/p).read_text()
patch=''
for n,s in sorted(rs.items()):
 if Path(n).name.startswith('PCG_'):old=''
 else:
  rev='b936275465600469312d1f058cdc91ea2a11f3dc' if n.startswith('programs/aspis-pool/') else '4bb3b3f51e16b4525f1d10336e2b0bcbbd775387'
  old=subprocess.check_output(['git','show',rev+':'+n],text=True)
 patch+=''.join(difflib.unified_diff(old.splitlines(True),s.splitlines(True),fromfile='a/'+n if old else '/dev/null',tofile='b/'+n))
(E/'PCG_HARNESS.patch').write_text(patch);(E/'PCG_HARNESS.patch.sha256').write_text(sha(patch.encode())+'\n')
used=[json.loads(l) for l in (E/'PCG_ATTEMPTS.jsonl').read_text().splitlines()];limits=dict(kani=110,lean=90,extract=12)
counts={k:sum(('lean' if r['kind'] in ['lean','link','audit'] else r['kind'])==k for r in used) for k in limits}
(E/'PCG_BUDGET.json').write_text(json.dumps(dict(limits=limits,used=counts),indent=1)+'\n')
for p in E.rglob('__pycache__'):
 import shutil;shutil.rmtree(p)
for p in list(E.rglob('*')):
 if p.is_file() and p.stat().st_size>20_000_000:
  raw=p.read_bytes();p.with_name(p.name+'.xz').write_bytes(lzma.compress(raw,preset=6));p.with_name(p.name+'.sha256').write_text(sha(raw)+'\n');p.unlink()
for p in E.rglob('*.xz'):
 h=p.with_suffix('').with_name(p.with_suffix('').name+'.sha256')
 if not h.exists():h.write_text(sha(lzma.decompress(p.read_bytes()))+'\n')
 else:assert h.read_text().strip()==sha(lzma.decompress(p.read_bytes())),str(p)
assert not [str(p) for p in E.rglob('*') if p.is_file() and p.stat().st_size>20_000_000]
print('PCG source patch, budget and file-size checks recorded')
