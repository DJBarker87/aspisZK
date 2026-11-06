"""Archive original-byte barrier logs and enforce per-file commit size limits."""
from pathlib import Path
import lzma,hashlib,shutil
E=Path(__file__).resolve().parent;n=0
for p in E.glob('PCE_L*-barrier-*.log'):
 raw=p.read_bytes();p.with_name(p.name+'.xz').write_bytes(lzma.compress(raw,preset=6));p.with_name(p.name+'.sha256').write_text(hashlib.sha256(raw).hexdigest()+'\n');p.unlink();n+=1
for p in E.rglob('__pycache__'):shutil.rmtree(p)
for p in E.rglob('*'):
 if p.is_file():assert p.stat().st_size<=20_000_000,('file over20MB',str(p))
verified=0
for p in E.rglob('*.xz'):
 sh=p.with_name(p.name[:-3]+'.sha256')
 if sh.exists():assert hashlib.sha256(lzma.decompress(p.read_bytes())).hexdigest()==sh.read_text().strip();verified+=1
print('Hygiene PASS: archived'+str(n)+' original-byte barrier logs; verified'+str(verified)+' compressed SHA pairs; no file over20MB or own Python cache.')
