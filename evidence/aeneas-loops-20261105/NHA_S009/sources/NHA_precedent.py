from pathlib import Path
import subprocess,json,hashlib
B=Path(__file__).resolve().parent;p=B/'NHA_source_inspection/NHA_PRECEDENT_aeneas-d860ac47-preserve-distinct-loop-input-abstractions.patch'
r=subprocess.run(['patch','--dry-run','-p1','-i',str(p)],cwd=B/'NHA_toolchain/aeneas',text=True,capture_output=True)
print(r.stdout+r.stderr)
(B/'NHA_PRECEDENT_CHECK.json').write_text(json.dumps(dict(command=['patch','--dry-run','-p1','-i',str(p)],exit=r.returncode,stdout=r.stdout,stderr=r.stderr,patch_sha256=hashlib.sha256(p.read_bytes()).hexdigest(),applied=False),indent=2))
