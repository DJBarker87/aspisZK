"""Read a retained logical input/log, verifying compressed/deduplicated bytes."""
from pathlib import Path
import hashlib,json,lzma,sys
E=Path(__file__).resolve().parent
def read_bytes(path):
 p=Path(path)
 if p.is_file():return p.read_bytes()
 z=Path(str(p)+'.xz')
 if z.is_file():
  b=lzma.decompress(z.read_bytes());h=Path(str(p)+'.sha256')
  assert h.is_file() and hashlib.sha256(b).hexdigest()==h.read_text().strip(),p
  return b
 index=json.loads((E/'NKE_INPUT_INDEX.json').read_text());r=index[str(p.resolve().relative_to(E))]
 q=E/r['retained'];b=lzma.decompress(q.read_bytes()) if r['compressed'] else q.read_bytes()
 assert len(b)==r['bytes'] and hashlib.sha256(b).hexdigest()==r['sha256'],p
 return b
def read_text(path):return read_bytes(path).decode()
if __name__=='__main__':sys.stdout.buffer.write(read_bytes(E/sys.argv[1]))
