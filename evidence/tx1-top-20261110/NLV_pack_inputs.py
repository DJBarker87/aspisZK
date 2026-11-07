"""Losslessly retain repeated large attempt inputs once by sha256.
Does not alter host/cache, receipts, Lean sources, commands or verdicts.
"""
from pathlib import Path
import hashlib,json,lzma
E=Path(__file__).resolve().parent;D=E/'NLV_pinned_inputs';D.mkdir(exist_ok=True);rows=[]
# Source snapshots are immutable evidence, not executable working inputs.
# Top-level sources/configs/receipts remain directly readable by our runners.
paths=[p for q in E.glob('NLV_[LK][0-9][0-9][0-9]/sources')for p in q.rglob('*')if p.is_file()and p.stat().st_size>=100_000 and not p.name.endswith('.ref.json')]
for p in paths:
 raw=p.read_bytes();h=hashlib.sha256(raw).hexdigest();q=D/('NLV_'+h+'.xz')
 if q.exists():assert lzma.decompress(q.read_bytes())==raw
 else:q.write_bytes(lzma.compress(raw,preset=0));q.with_suffix('.sha256').write_text(h+'\n')
 ref=dict(owned_input=str(q.relative_to(E)),sha256=h,bytes=len(raw),compression='xz',stored_sha256=hashlib.sha256(q.read_bytes()).hexdigest())
 p.with_name(p.name+'.ref.json').write_text(json.dumps(ref,indent=2));rows.append(dict(original=str(p.relative_to(E)),**ref));p.unlink()
(E/'NLV_INPUT_PACKING.json').write_text(json.dumps(dict(policy='Lossless content-addressed evidence input snapshots; host untouched; original hash and compressed hash retained',packed=rows),indent=2));print('Packed',len(rows),'repeated large source snapshots')
