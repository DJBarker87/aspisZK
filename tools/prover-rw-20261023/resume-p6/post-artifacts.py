"""Read own generated artifact identities, never copy object or large JSON bytes."""
from pathlib import Path
import hashlib,json,subprocess
D=Path(__file__).resolve().parent
rows=[]
for tag,base in [('original',D),('compact',D/'compact')]:
 for p in sorted((base/'target').rglob('*')):
  if not p.is_file():continue
  if p.suffix not in ['.json','.goto','.symtab','.rlib','.rmeta','.o'] and not p.name.endswith('kani-metadata.json'):continue
  h=hashlib.sha256()
  with p.open('rb') as f:
   for block in iter(lambda:f.read(1024*1024),b''):h.update(block)
  rows.append(dict(version=tag,path=str(p.relative_to(D)),size=p.stat().st_size,sha256=h.hexdigest()))
version=subprocess.run(['/home/dombarker/.kani/kani-0.67.0/toolchain/bin/rustc','-vV'],text=True,capture_output=True)
print(json.dumps(dict(schema='ProverRwResumeP6-artifact-identities-v1',artifacts=rows,rustc_version=dict(command=version.args,exit=version.returncode,stdout=version.stdout,stderr=version.stderr),content_policy='hash+size only; no derived JSON/object/binary content copied',print_axioms='N/A: read-only artifact inventory'),indent=2))
