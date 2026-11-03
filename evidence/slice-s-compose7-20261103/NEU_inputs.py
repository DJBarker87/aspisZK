"""Exact JSON input with hash-checked rule-12 transport for the large overlay."""
from pathlib import Path
import json,lzma,hashlib

def read(path):
 p=Path(path)
 if p.is_file():return json.loads(p.read_text())
 assert p.name=='NEU_LEDGER_DELTA.json','missing input: '+str(p)
 data=lzma.decompress(Path(str(p)+'.xz').read_bytes())
 assert hashlib.sha256(data).hexdigest()==Path(str(p)+'.sha256').read_text().strip(),'uncompressed input hash mismatch'
 return json.loads(data)

def write_delta(path,data):
 p=Path(path);assert p.name=='NEU_LEDGER_DELTA.json'
 raw=(json.dumps(data,separators=(',',':'))+'\n').encode()
 packed=lzma.compress(raw,preset=6)
 assert lzma.decompress(packed)==raw
 Path(str(p)+'.xz').write_bytes(packed)
 Path(str(p)+'.sha256').write_text(hashlib.sha256(raw).hexdigest()+'\n')
 if p.exists():p.unlink()
