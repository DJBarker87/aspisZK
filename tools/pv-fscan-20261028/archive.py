from pathlib import Path
import hashlib,json,lzma
D=Path('/home/dombarker/project-offloads/codex-pv-fscan-20261028');out=[]
for p in sorted(D.glob('*/crate.mir')):
 b=p.read_bytes();z=p.with_suffix('.mir.xz');z.write_bytes(lzma.compress(b,preset=6));out.append(dict(path=str(p.relative_to(D)),sha256=hashlib.sha256(b).hexdigest(),size=len(b),xz_size=z.stat().st_size))
(D/'dump-manifest.json').write_text(json.dumps(out,indent=2));print('archived',len(out),'MIR text files',sum(x['xz_size'] for x in out),'compressed bytes')
