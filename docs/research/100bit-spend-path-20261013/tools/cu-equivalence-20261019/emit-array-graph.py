#!/usr/bin/env python3
"""Promote exact successful library declarations, excluding arithmetic callers."""
from pathlib import Path
import argparse,hashlib,json
ap=argparse.ArgumentParser();ap.add_argument('--check',action='store_true');args=ap.parse_args()
here=Path(__file__).resolve().parent;area=here.parents[1];sha=lambda b:hashlib.sha256(b).hexdigest()
pins={};outputs={}
for name,expected,marker in [
 ('Types.lean','00b3f7c124f10d09fd2d494224afab3a0206b35ca924bed0c4d60c9a1a2e1590',b'/-- [aspis_r1_cu_dots::fast_pairing::canonical::Dot]'),
 ('Funs.lean','c3b5d65faf2a10654e0de6aeafc1a0b004f116cb7639acd8847c973758a71dd3',b'/-- [aspis_r1_cu_dots::field::wide_exact::')]:
    raw=(here/'array-graph-generated'/name).read_bytes();assert sha(raw)==expected
    end=raw.index(marker);selected=raw[:end]
    assert b'sorry' not in selected and b'axiom ' not in selected
    output=selected+b'end AspisR1CuArrayGraph\n'
    outputs[area/'lean/AspisR1CuArrayGraph'/name]=output
    pins[name]=dict(source_sha256=sha(raw),first=0,last=end,selected_sha256=sha(selected),output_sha256=sha(output))
outputs[here/'array-graph-emission.json']=(json.dumps(dict(cuts=pins,
    status='EXACT_EMITTED_LIBRARY_UNDER_EXPLICIT_PRIMITIVE_MODELS',
    scope='Complete emitted from_fn, try_from_fn and erased loop; bodies unchanged. Runtime graph model checked separately. Primitive/frontend admission and consuming builder equivalence remain required.'),indent=2)+'\n').encode()
for path,data in outputs.items():
    if args.check:assert path.read_bytes()==data,str(path)
    else:path.parent.mkdir(parents=True,exist_ok=True);path.write_bytes(data)
print(json.dumps(dict(check=args.check,library_bodies_unchanged=True)))
