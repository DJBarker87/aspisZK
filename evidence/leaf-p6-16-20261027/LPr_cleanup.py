from pathlib import Path
import subprocess,shlex,json,time
E=Path(__file__).resolve().parent
B='/home/dombarker/project-offloads/codex-cx-leaf-p6-16-20261027'
code='''from pathlib import Path
import hashlib,json,shutil
b=Path(%r);p=b/'LPr_objects'
assert p.parent==b and p.name=='LPr_objects'
pins={str(f.relative_to(b)):dict(sha256=hashlib.sha256(f.read_bytes()).hexdigest(),bytes=f.stat().st_size) for f in p.rglob('*') if f.is_file()}
if p.exists():shutil.rmtree(p)
print(json.dumps(dict(removed=str(p),objects=pins,remaining_sources=True)))
''' % B
# Cleanup executes once. On transport loss, inspect read-only; never repeat it.
r=subprocess.run(['ssh','-o','ConnectTimeout=15','dombarker@100.108.41.90','python3 -c '+shlex.quote(code)],capture_output=True,text=True)
(E/'LPr_CLEANUP_TRANSPORT.json').write_text(json.dumps(dict(exit=r.returncode,stdout=r.stdout,stderr=r.stderr),indent=2)+'\n')
assert r.returncode==0,r.stderr
(E/'LPr_CLEANUP.json').write_text(json.dumps(json.loads(r.stdout),indent=2)+'\n')
