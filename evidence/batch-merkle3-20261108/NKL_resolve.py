"""Lossless access to committed, SHA-pinned evidence inputs."""
from pathlib import Path
import hashlib,json,lzma
E=Path(__file__).resolve().parent
def read(name):
 p=E/name
 if p.is_file():return p.read_bytes()
 q=p.with_name(p.name+'.xz')
 if q.is_file():
  data=lzma.decompress(q.read_bytes());assert hashlib.sha256(data).hexdigest()==p.with_name(p.name+'.sha256').read_text().strip();return data
 refs=json.loads((E/'NKL_POOLED_INPUTS.json').read_text());x=refs[name]
 data=(E/x['file']).read_bytes() if 'file' in x else lzma.decompress((E/x['pool']).read_bytes())
 assert len(data)==x['bytes'] and hashlib.sha256(data).hexdigest()==x['sha256'];return data
