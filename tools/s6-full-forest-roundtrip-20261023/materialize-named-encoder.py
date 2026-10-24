#!/usr/bin/env python3
"""Fresh namespace and type-qualified instance for the unchanged full encoder cut."""
from pathlib import Path
import hashlib,json,sys
R=Path(__file__).resolve().parents[2];B=R/'docs/research/100bit-spend-path-20261013';S=B/'lean-candidates/s126-caller-boundary-20261021';E=B/'evidence/s126-current-caller-20261021'
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
rows={}
for kind in ['Types','Native']:
 original=S/('S6FullForestEncoder'+kind+'V1.lean');text=original.read_text().replace('AspisS6FullForestEncoder','AspisS6FullForestEncoderNamed')
 if kind=='Types':
  assert text.count('@[discriminant u8 [1,2]]')==1
  text=text.replace('import Aeneas','import S6NamedDiscriminantV1',1).replace('@[discriminant u8 [1,2]]','@[s6_u8_discriminant]')
 else:text=text.replace('import S6FullForestEncoderTypesV1','import S6FullForestEncoderNamedTypesV1',1)
 target=S/('S6FullForestEncoderNamed'+kind+'V1.lean')
 if '--check' in sys.argv:assert target.read_text()==text
 else:target.write_text(text)
 rows[str(target.relative_to(R))]=dict(original=str(original.relative_to(R)),original_sha256=sha(original),candidate_sha256=hashlib.sha256(text.encode()).hexdigest())
meta=dict(schema='focused-extractor-proof-packet-v1',sources=rows,qualification='Namespace-only copy of existing full generated nominal carriers and full encoder body. The reused Aeneas naming adapter changes only instance names; original enum tags/readers retained. No body, field or child port simplified; concrete child and carrier joins remain required.')
p=E/'s6-outer-named-materialization.json'
if '--check' in sys.argv:assert json.loads(p.read_text())==meta
else:p.write_text(json.dumps(meta,indent=2)+'\n')
