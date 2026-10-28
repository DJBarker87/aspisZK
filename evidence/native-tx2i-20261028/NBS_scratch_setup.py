from pathlib import Path
import subprocess,shlex,json
E=Path(__file__).resolve().parent
code='''from pathlib import Path
import hashlib,json
b=Path('/home/dombarker/project-offloads/codex-cx-native-tx2i-20261028')
s=Path('/home/dombarker/project-offloads/codex-cx-native-tx2h-20261028/NBQ_src')
assert s.is_dir()
p=b/'NBS_src'
if not p.exists():p.symlink_to(s,target_is_directory=True)
assert p.resolve()==s
print(json.dumps(dict(reused_scratch=str(s),lock_sha256=hashlib.sha256((s/'Cargo.lock').read_bytes()).hexdigest(),inherited_patches=[str(x) for x in s.parent.glob('NBQ_*-harness.patch')])))
'''
r=subprocess.run(['ssh','-o','ConnectTimeout=15','dombarker@100.108.41.90','python3 -c '+shlex.quote(code)],capture_output=True,text=True)
(E/'NBS_SCRATCH_REUSE.json').write_text(json.dumps(dict(exit=r.returncode,stdout=r.stdout,stderr=r.stderr),indent=2)+'\n')
assert r.returncode==0,r.stderr
