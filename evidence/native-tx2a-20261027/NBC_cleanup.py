"""Remove confirmed terminal build outputs only; retain all sources and keys."""
from pathlib import Path
import subprocess,shlex,json
E=Path(__file__).resolve().parent
terminal=json.loads((E/'NBC_TERMINAL_HOST.json').read_text())
assert all(r['terminal'] for r in terminal['scopes'])
B='/home/dombarker/project-offloads/codex-cx-native-tx2a-20261027'
code=f'''from pathlib import Path
import json,shutil
b=Path({B!r});receipt=b/'NBC_CLEANUP.json'
assert not receipt.exists(),'recover previous cleanup read-only'
for p in b.glob('NBC_[KL]*/receipt.json'):
 r=json.loads(p.read_text());cg=Path(r['cgroup'])
 assert not cg.exists() or not (cg/'cgroup.procs').read_text().strip(),str(cg)
removed={{}}
for name in ['NBC_target','NBC_tmp']:
 p=b/name
 assert p.parent==b and not p.is_symlink()
 if p.exists():
  removed[name]=dict(files=sum(1 for q in p.rglob('*') if q.is_file()),bytes=sum(q.stat().st_size for q in p.rglob('*') if q.is_file()))
  shutil.rmtree(p)
out=dict(removed=removed,all_build_outputs_absent=all(not (b/n).exists() for n in ['NBC_target','NBC_tmp']),source_scratch_retained=(b/'NBC_src').exists(),persistent_cache_retained=Path('/home/dombarker/project-offloads/codex-cx-leaf-cache-20261027').is_dir(),keys_deleted=False)
receipt.write_text(json.dumps(out,indent=2)+'\\n');print(json.dumps(out))
'''
r=subprocess.run(['ssh','-o','ConnectTimeout=15','dombarker@100.108.41.90','python3 -c '+shlex.quote(code)],capture_output=True,text=True)
(E/'NBC_CLEANUP_TRANSPORT.json').write_text(json.dumps(dict(exit=r.returncode,stdout=r.stdout,stderr=r.stderr))+'\n')
assert r.returncode==0,'recover NBC_CLEANUP.json read-only; no resubmission'
(E/'NBC_CLEANUP.json').write_text(json.dumps(json.loads(r.stdout),indent=2)+'\n');print(r.stdout)
