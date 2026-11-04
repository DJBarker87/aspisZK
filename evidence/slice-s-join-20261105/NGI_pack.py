"""Keep repeated large receipt inputs once, with original SHA256 references."""
from pathlib import Path
import json,hashlib,lzma
E=Path(__file__).resolve().parent;H=lambda b:hashlib.sha256(b).hexdigest();records=json.loads((E/'NGI_PACK.json').read_text())['references'] if (E/'NGI_PACK.json').exists() else []
for p in sorted(E.glob('NGI_L*/sources/**/*')):
 if not p.is_file() or (p.stat().st_size<65536 and p.suffix!='.c'):continue
 raw=p.read_bytes();h=H(raw);top=E/p.name
 if top.is_file() and top!=p and top.read_bytes()==raw:
  target=top;kind='uncompressed'
 else:
  target=E/'NGI_pinned_inputs'/(h+'.xz');target.parent.mkdir(exist_ok=True)
  if not target.exists():target.write_bytes(lzma.compress(raw,preset=6));target.with_suffix('.sha256').write_text(h+'\n')
  assert H(lzma.decompress(target.read_bytes()))==h;kind='xz'
 ref=dict(original_path=str(p.relative_to(E)),sha256=h,bytes=len(raw),stored_once=str(target.relative_to(E)),encoding=kind)
 p.with_name(p.name+'.REFERENCE.json').write_text(json.dumps(ref,indent=1)+'\n');p.unlink();records.append(ref)
# Preserve source log bytes while avoiding generated-C whitespace churn in diffs.
for p in sorted(E.glob('NGI_L*-barrier-*.log')):
 raw=p.read_bytes();q=Path(str(p)+'.xz');q.write_bytes(lzma.compress(raw));Path(str(p)+'.sha256').write_text(H(raw)+'\n');p.unlink()
(E/'NGI_PACK.json').write_text(json.dumps(dict(references=records,no_input_discarded=True),indent=1)+'\n')
for p in E.rglob('*'):
 if p.is_file():assert p.stat().st_size<=20*1024**2,p
print('Packed',len(records),'large repeated input snapshots')
