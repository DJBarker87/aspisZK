"""Keep repeated complete metadata once, addressed by uncompressed SHA256."""
from pathlib import Path
import hashlib,json,lzma
E=Path(__file__).resolve().parent;directory=E/'NHU_INPUTS';directory.mkdir(exist_ok=True)
p=E/'NHU_METADATA_MANIFEST.json';manifest=json.loads(p.read_text()) if p.exists() else {}
for source in sorted(E.glob('NHU_K???-graph.json')):
 raw=source.read_bytes();h=hashlib.sha256(raw).hexdigest();artifact=directory/(h+'.json.xz')
 if not artifact.exists():artifact.write_bytes(lzma.compress(raw,preset=6))
 assert hashlib.sha256(lzma.decompress(artifact.read_bytes())).hexdigest()==h
 (directory/(h+'.json.sha256')).write_text(h+'\n')
 manifest[source.name]=dict(artifact=str(artifact.relative_to(E)),sha256=h,bytes=len(raw))
 source.unlink()
p.write_text(json.dumps(manifest,indent=1))
print(json.dumps(dict(metadata_names=len(manifest),unique_artifacts=len({r['artifact'] for r in manifest.values()}))))
