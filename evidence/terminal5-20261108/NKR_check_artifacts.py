from pathlib import Path
import hashlib,json,base64,lzma,datetime
E=Path(__file__).resolve().parent
count=0;total=0
for f in sorted((E/'NKR_audit').glob('proof*/*.xz.b64.txt')):
 raw=lzma.decompress(base64.b64decode(f.read_bytes(),validate=True));q=f.with_name(f.name[:-len('.xz.b64.txt')]+'.sha256');assert hashlib.sha256(raw).hexdigest()==q.read_text().strip(),str(f);count+=1;total+=len(raw)
assert count==10503,count
r=dict(checked_utc=datetime.datetime.now(datetime.timezone.utc).isoformat(),compressed_raw_artifacts=count,uncompressed_bytes=total,sha256_verified=True)
(E/'NKR_ARTIFACT_CHECK.json').write_text(json.dumps(r,indent=1)+'\n');print(json.dumps(r))
