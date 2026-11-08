"""Preserve generated linker inputs byte-for-byte without text normalization."""
from pathlib import Path
import hashlib,lzma,json
E=Path(__file__).resolve().parent
for p in (E/'NNO_native').glob('*.c'):
 raw=p.read_bytes();Path(str(p)+'.xz').write_bytes(lzma.compress(raw,preset=6));Path(str(p)+'.sha256').write_text(hashlib.sha256(raw).hexdigest()+'\n');p.unlink()
rows=json.loads((E/'NNO_LINK_INPUTS.json').read_text())
for x in rows:
 name=Path(x['path']).name;x['retained_archive']='NNO_native/'+name+'.xz';assert hashlib.sha256(lzma.open(E/x['retained_archive']).read()).hexdigest()==x['sha256']
(E/'NNO_LINK_INPUTS.json').write_text(json.dumps(rows,indent=1)+'\n')
