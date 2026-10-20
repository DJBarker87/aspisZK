#!/usr/bin/env python3
"""Private union of retained package objects; never change shared caches."""
from pathlib import Path
import json,hashlib
here=Path(__file__).resolve().parent
base=json.loads((here.parent/'headline-20261021/R1FinalSoundnessHeadline-2/command.json').read_text())
overlay=Path('/tmp/codex-cx-r4-transport-20261021-imports')
paths=['/tmp/prepared-local-warm-cache-20261020','/tmp/codex-cx-r4-transport-upstream-objects']+base['lean_path'].split(':')+['/tmp/codex-cx-r14-finish-20261020-objects']
excluded={'Mathlib','Aeneas','AeneasMeta','Lean','Init','Std','Lake','Aesop','Batteries','Qq','Plausible','ProofWidgets','ImportGraph','LeanSearchClient','LeanSearchClientCompat'}
packages=sorted({p.name for d in paths if Path(d).is_dir() for p in Path(d).iterdir()
    if p.is_dir() and p.name not in excluded and not p.name.startswith('.')})

rows=[]
for package in packages:
 for directory in paths:
  root=Path(directory)/package
  if not root.is_dir():continue
  for src in sorted(root.rglob('*.olean')):
   if not src.is_file(): continue
   relative=Path(package)/src.relative_to(root)
   dest=overlay/relative
   if dest.is_symlink() and not dest.exists(): dest.unlink()
   if not dest.exists():
    dest.parent.mkdir(parents=True,exist_ok=True);dest.symlink_to(src)
 for src in sorted((overlay/package).rglob('*.olean')) if (overlay/package).exists() else []:
  if not src.is_file(): continue
  sidecars=[]
  for suffix in ['.server','.private']:
   extra=Path(str(src.resolve())+suffix)
   dest=Path(str(src)+suffix)
   if extra.is_file():
    if not dest.exists(): dest.symlink_to(extra)
    sidecars.append({'path':str(extra),'sha256':hashlib.sha256(extra.read_bytes()).hexdigest(),'bytes':extra.stat().st_size})
  extra=src.resolve().with_suffix('.ir')
  dest=src.with_suffix('.ir')
  if extra.is_file():
   if not dest.exists(): dest.symlink_to(extra)
   sidecars.append({'path':str(extra),'sha256':hashlib.sha256(extra.read_bytes()).hexdigest(),'bytes':extra.stat().st_size})
  rows.append({'sidecars':sidecars,'module':str(src.relative_to(overlay))[:-6].replace('/','.'),'object':str(src.resolve()),'sha256':hashlib.sha256(src.read_bytes()).hexdigest(),'bytes':src.stat().st_size})
(here/'import-overlay.json').write_text(json.dumps({'overlay':str(overlay),'priority':paths,'objects':rows},indent=2)+'\n')
print(len(rows),'retained objects linked, no modules rebuilt')
