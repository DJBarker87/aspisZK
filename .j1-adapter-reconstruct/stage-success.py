from pathlib import Path
import hashlib,json,shutil
p=Path('docs/research/100bit-spend-path-20261013/lean/ExtractedAdapterReconstructSuccess.lean')
proof=Path('.j1-adapter-reconstruct/proofs')
m=json.loads((proof/'sources/SOURCE-MANIFEST.json').read_text())
m['modules'][p.stem]['source_sha256']=hashlib.sha256(p.read_bytes()).hexdigest()
(proof/'sources/SOURCE-MANIFEST.json').write_text(json.dumps(m,indent=2)+'\n')
shutil.copy2(p,proof/'sources'/p.name)
print(m['modules'][p.stem]['source_sha256'])
