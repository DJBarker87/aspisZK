from pathlib import Path
import hashlib,lzma,json
E=Path(__file__).resolve().parent;rows=[]
for p in sorted(E.rglob('*')):
 if not p.is_file()or p.suffix in ['.xz','.sha256']:continue
 b=p.read_bytes();whitespace=p.suffix=='.log'and(b.endswith(b'\n\n')or any(l.endswith((b' ',b'\t'))for l in b.splitlines()))
 if len(b)<=20_000_000 and not whitespace:continue
 h=hashlib.sha256(b).hexdigest();z=Path(str(p)+'.xz');z.write_bytes(lzma.compress(b,preset=6));Path(str(p)+'.sha256').write_text(h+'\n');assert hashlib.sha256(lzma.decompress(z.read_bytes())).hexdigest()==h;p.unlink();rows.append(dict(path=str(p.relative_to(E)),bytes=len(b),sha256=h,reason='Preserve exact raw log whitespace in compressed evidence'if whitespace else'20MB limit'))
old=E/'NJO_PACKAGING.json';prior=json.loads(old.read_text())['archives']if old.exists()else[]
old.write_text(json.dumps(dict(status='PASS',raw_bytes_preserved=True,archives=prior+rows,all_uncompressed_sha_recorded=True),indent=1)+'\n');print(json.dumps(dict(stage='package',raw_logs_archived=len(rows))))
