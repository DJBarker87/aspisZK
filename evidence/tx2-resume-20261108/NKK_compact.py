from pathlib import Path
import hashlib,json,lzma
E=Path(__file__).resolve().parent;D=E/'NKK_inputs';D.mkdir(exist_ok=True)
p=E/'NKK_INPUT_INDEX.json';index=json.loads(p.read_text()) if p.exists() else {}
for attempt in sorted(E.glob('NKK_[LK][0-9][0-9][0-9]')):
 if not (attempt/'receipt.json').exists():continue
 for src in sorted((attempt/'sources').rglob('*')):
  if not src.is_file():continue
  b=src.read_bytes();h=hashlib.sha256(b).hexdigest();target=D/(h+'.xz')
  if not target.exists():target.write_bytes(lzma.compress(b,preset=6))
  index[str(src.relative_to(E))]=dict(sha256=h,bytes=len(b),capsule=str(target.relative_to(E)))
  src.unlink()
 for d in sorted((attempt/'sources').rglob('*'),reverse=True):
  if d.is_dir():d.rmdir()
 if (attempt/'sources').exists():(attempt/'sources').rmdir()
for src in sorted(E.rglob('*.log')):
 if src.stat().st_size<100_000:continue
 b=src.read_bytes();src.with_name(src.name+'.sha256').write_text(hashlib.sha256(b).hexdigest()+'\n');src.with_name(src.name+'.xz').write_bytes(lzma.compress(b,preset=6));src.unlink()
p.write_text(json.dumps(index,indent=2)+'\n')
print(json.dumps(dict(source_snapshots=len(index),unique_capsules=len(list(D.glob('*.xz'))))))
