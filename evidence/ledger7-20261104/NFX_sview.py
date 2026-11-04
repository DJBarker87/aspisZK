from pathlib import Path
import shutil,json,hashlib,lzma
P=Path('/home/dombarker/project-offloads');S=P/'codex-cx-slice-s-compose12-cache-20261104';D=P/'codex-cx-ledger7-cache-20261104/NFX_S_view';B=P/'codex-cx-ledger7-20261104'
shutil.copytree(S,D,dirs_exist_ok=True)
rows=[]
for p in sorted(D.rglob('*')):
 if p.is_file():rows.append(dict(path=str(p),source=str(S/p.relative_to(D)),sha256=hashlib.sha256(p.read_bytes()).hexdigest(),bytes=p.stat().st_size))
raw=json.dumps(rows,sort_keys=True).encode();(B/'NFX_SVIEW_PINS.json.xz').write_bytes(lzma.compress(raw));(B/'NFX_SVIEW_PINS.json.sha256').write_text(hashlib.sha256(raw).hexdigest()+'\n');print(len(rows))
