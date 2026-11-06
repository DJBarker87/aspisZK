"""Lossless access to deduplicated evidence inputs (paths relative to this directory)."""
from pathlib import Path
import hashlib,json,lzma
E=Path(__file__).resolve().parent
def read(name):
 p=E/name
 if p.is_file():return p.read_bytes()
 if p.with_name(p.name+'.xz').is_file():
  data=lzma.decompress(p.with_name(p.name+'.xz').read_bytes())
  assert hashlib.sha256(data).hexdigest()==p.with_name(p.name+'.sha256').read_text().strip()
  return data
 refs=E/'NJS_POOLED_INPUTS.json'
 x=json.loads(refs.read_text())[name];data=lzma.decompress((E/x['pool']).read_bytes())
 assert len(data)==x['bytes'] and hashlib.sha256(data).hexdigest()==x['sha256']
 return data
