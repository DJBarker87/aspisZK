"""Pack completed raw per-root evidence, preserving every member byte."""
from pathlib import Path
import json,hashlib,lzma,tarfile,io
E=Path(__file__).resolve().parent
assert(E/'NMC_AUDIT.json').exists()and not(E/'NMC_CLIENT_ACTIVE').exists()
assert not(E/'NMC_RAW_ARCHIVES.json').exists()
H=lambda b:hashlib.sha256(b).hexdigest()
rows=[]
for n in range(30):
 d=E/'NMC_audit'/f'proof{n}';files=sorted(p for p in d.iterdir()if p.is_file()and p.name.startswith('NEP_'))
 assert files
 expected={p.name:H(p.read_bytes())for p in files};stream=io.BytesIO()
 with tarfile.open(fileobj=stream,mode='w')as tar:
  for p in files:
   blob=p.read_bytes();info=tarfile.TarInfo(p.name);info.size=len(blob);info.mode=0o644;info.mtime=0
   tar.addfile(info,io.BytesIO(blob))
 raw=stream.getvalue();packed=lzma.compress(raw)
 assert len(packed)<=20_000_000
 out=d/(d.name+'.tar.xz');out.write_bytes(packed)
 out.with_name(d.name+'.tar.sha256').write_text(H(raw)+'\n')
 with tarfile.open(fileobj=io.BytesIO(lzma.decompress(out.read_bytes())),mode='r')as tar:
  observed={m.name:H(tar.extractfile(m).read())for m in tar.getmembers()}
 assert observed==expected
 rows.append(dict(group=d.name,archive=str(out.relative_to(E)),tar_sha256=H(raw),xz_sha256=H(packed),members=len(files),original_bytes=sum(p.stat().st_size for p in files),tar_bytes=len(raw),xz_bytes=len(packed)))
 for p in files:p.unlink()
manifest=dict(status='PASS_BYTE_EXACT_RAW_ARCHIVES',groups=rows,members=sum(r['members']for r in rows),original_bytes=sum(r['original_bytes']for r in rows),packed_bytes=sum(r['xz_bytes']for r in rows),proofs_repeated=0)
(E/'NMC_RAW_ARCHIVES.json').write_text(json.dumps(manifest,indent=2)+'\n')
a=json.loads((E/'NMC_AUDIT.json').read_text());a['raw_storage']=dict(index='NMC_RAW_ARCHIVES.json',status=manifest['status'],groups=30,members=manifest['members'],proofs_repeated=0);(E/'NMC_AUDIT.json').write_text(json.dumps(a,indent=2)+'\n')
print(json.dumps({k:v for k,v in manifest.items()if k!='groups'}))
