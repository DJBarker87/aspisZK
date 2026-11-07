"""Verify raw archive bytes; --materialize restores the original files locally."""
from pathlib import Path
import json,hashlib,lzma,tarfile,io,sys
E=Path(__file__).resolve().parent
assert sys.argv[1:]in [[],['--materialize']]
H=lambda b:hashlib.sha256(b).hexdigest()
x=json.loads((E/'NMC_RAW_ARCHIVES.json').read_text());count=0
for row in x['groups']:
 p=E/row['archive'];packed=p.read_bytes();assert H(packed)==row['xz_sha256'];raw=lzma.decompress(packed);assert H(raw)==row['tar_sha256']
 assert H(raw)==p.with_name(row['group']+'.tar.sha256').read_text().strip()
 with tarfile.open(fileobj=io.BytesIO(raw),mode='r')as tar:
  members=tar.getmembers();assert len(members)==row['members']
  for m in members:
   assert m.isfile()and Path(m.name).name==m.name
   if sys.argv[1:]:
    blob=tar.extractfile(m).read();dest=p.parent/m.name
    if dest.exists():assert dest.read_bytes()==blob
    else:dest.write_bytes(blob)
  count+=len(members)
assert count==x['members']
print(json.dumps(dict(status='PASS_RAW_ARCHIVE_HASHES',members=count,materialized=bool(sys.argv[1:]),proofs_launched=0)))
