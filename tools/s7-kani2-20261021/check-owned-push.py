#!/usr/bin/env python3
from pathlib import Path
import hashlib,json,re
R=Path(__file__).resolve().parents[2];B=R/'docs/research/100bit-spend-path-20261013'
p=B/'evidence/s7-kani-20261021/extraction/generated/S7OwnedP6/Funs.lean'
s=p.read_text();a=s.index('def push_owned\n');b=s.index('/--',a);original=s[a:b].strip()
q=B/'lean/S7Kani2OwnedPush.lean';s=q.read_text();a=s.index('def push_owned ');b=s.index('/--',a);port=s[a:b].strip()
normalized=original.replace('aspis_core.field.QM31','K').replace('aspis_core.field.M31','U32').replace('Std.','').replace('«raw»','raw')
norm=lambda s:re.sub(r'\s+','',s)
assert norm(normalized)==norm(port)
r=dict(source=str(p.relative_to(R)),source_sha256=hashlib.sha256(p.read_bytes()).hexdigest(),declaration_sha256=hashlib.sha256(original.encode()).hexdigest(),port=str(q.relative_to(R)),port_declaration_sha256=hashlib.sha256(port.encode()).hexdigest(),edits='Whitespace, exact U32 carrier alias, structural K carrier, Std qualification, raw identifier escaping only; all indexing, mask, scalar-row call, mutable setter and state reconstruction operations retained.',normalized_equal=True)
(B/'evidence/s7-kani2-20261021/owned-push-binding.json').write_text(json.dumps(r,indent=2)+'\n')
print('Actual emitted owned push preserved modulo recorded carrier names')
