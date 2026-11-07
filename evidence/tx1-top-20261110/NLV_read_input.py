"""Read/verify an evidence input, following its lossless content-addressed ref.
Usage: python3 NLV_read_input.py path [output-path]. Omit output to verify only.
"""
from pathlib import Path
import hashlib,json,lzma,sys
E=Path(__file__).resolve().parent;p=Path(sys.argv[1]);p=p if p.is_absolute()or p.exists()or p.with_name(p.name+'.ref.json').exists()else E/p
if p.exists():raw=p.read_bytes()
else:
 ref=json.loads(p.with_name(p.name+'.ref.json').read_text());q=E/ref['owned_input'];assert hashlib.sha256(q.read_bytes()).hexdigest()==ref['stored_sha256'];raw=lzma.decompress(q.read_bytes());assert len(raw)==ref['bytes']and hashlib.sha256(raw).hexdigest()==ref['sha256']
if len(sys.argv)>2:Path(sys.argv[2]).write_bytes(raw)
print(json.dumps(dict(bytes=len(raw),sha256=hashlib.sha256(raw).hexdigest(),verified=True)))
