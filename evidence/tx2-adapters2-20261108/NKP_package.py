from pathlib import Path
import lzma,json,hashlib,shutil
b=Path.cwd();rows=[]
for p in sorted(b.glob('NEP_*_REACHABLE.txt')):
 raw=p.read_bytes();out=b/('NKP_'+p.name+'.xz');compressed=lzma.compress(raw,preset=6);out.write_bytes(compressed)
 assert lzma.decompress(compressed)==raw
 h=hashlib.sha256(raw).hexdigest();(b/('NKP_'+p.name+'.sha256')).write_text(h+'\n')
 rows.append(dict(source=str(p),archive=out.name,sha256=h,bytes=len(raw),archive_bytes=len(compressed),archive_sha256=hashlib.sha256(compressed).hexdigest()))
assert len(rows)==80,len(rows)
owned=sum(p.stat().st_size for p in b.rglob('*') if p.is_file())
obj=dict(files=rows,owned_retained_file_bytes=owned,retained_limit_bytes=30_000_000_000,free_bytes=shutil.disk_usage(b).free,uncompressed_diagnostics_retained=True,caches_and_tmpdir_retained=True)
assert owned<30_000_000_000
(b/'NKP_PACKAGING.json').write_text(json.dumps(obj,indent=1)+'\n')
print(json.dumps(dict(packaged=len(rows),raw_bytes=sum(x['bytes'] for x in rows),archive_bytes=sum(x['archive_bytes'] for x in rows),own_retained_bytes=owned,free_bytes=obj['free_bytes'])))
