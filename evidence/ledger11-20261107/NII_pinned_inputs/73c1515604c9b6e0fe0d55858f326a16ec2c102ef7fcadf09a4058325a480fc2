from pathlib import Path
import json,lzma,hashlib
E=Path(__file__).resolve().parent

def raw(path):
 p=Path(path)
 if p.exists():return p.read_bytes()
 ref=Path(str(p)+'.ref.json')
 if ref.exists():
  x=json.loads(ref.read_text());q=E/x['target'];q.resolve().relative_to(E.resolve())
  b=q.read_bytes();b=lzma.decompress(b) if x['encoding']=='xz' else b
  assert len(b)==x['bytes'] and hashlib.sha256(b).hexdigest()==x['sha256'],p
  return b
 z=Path(str(p)+'.xz')
 if z.exists():
  b=lzma.decompress(z.read_bytes());assert hashlib.sha256(b).hexdigest()==Path(str(p)+'.sha256').read_text().strip(),p
  return b
 raise FileNotFoundError(p)
def text(p):return raw(p).decode()
def read(p):return json.loads(text(p))
