#!/usr/bin/env python3
"""Select only the successful Guard declaration; never admit partial failures."""
from pathlib import Path
import argparse,hashlib,json
ap=argparse.ArgumentParser();ap.add_argument('--check',action='store_true');args=ap.parse_args()
here=Path(__file__).resolve().parent;area=here.parents[1]
sha=lambda b:hashlib.sha256(b).hexdigest()
raw={name:(here/'array-guard-generated'/name).read_bytes() for name in ['Types.lean','Funs.lean']}
assert sha(raw['Types.lean'])=='f029e4a5ab88e0bc1f10a4d6f98d936cabea7f0b9daddae7ea9e22467261f345'
assert sha(raw['Funs.lean'])=='c54977eb154335a18e2b394257c6c49d74a63fe888b72a9454d7868951a6714c'
cuts={
 'Types.lean':(b'/-- [core::array::Guard]',b'/-- [aspis_r1_cu_dots::fast_pairing::canonical::Dot]'),
 'Push.lean':(b'/-- [core::array::{core::array::Guard',b'/-- [core::array::try_from_fn_erased]')}
outputs={};pins={}
for name,(start,end) in cuts.items():
    source='Types.lean' if name=='Types.lean' else 'Funs.lean'
    body=raw[source];first=body.index(start);last=body.index(end,first);selected=body[first:last]
    assert b'sorry' not in selected and b'axiom ' not in selected
    imports=(b'import Aeneas\n' if name=='Types.lean' else b'import AspisR1CuArraySource.Primitives\n')
    header=b'-- Exact selected emitted declaration; body unchanged.\n'+imports
    header+=b'open Aeneas Aeneas.Std Result ControlFlow Error\nnamespace AspisR1CuArraySource\n'
    if name=='Types.lean':
        header+=b'\n-- Explicit initialized/uninitialized primitive interpretation, not a type axiom.\nabbrev core.mem.maybe_uninit.MaybeUninit (T : Type) := Option T\n\n'
    output=header+selected+b'end AspisR1CuArraySource\n'
    outputs[area/'lean/AspisR1CuArraySource'/name]=output
    pins[name]=dict(source=source,input_sha256=sha(body),first=first,last=last,
        selected_sha256=sha(selected),output_sha256=sha(output))
outputs[here/'array-guard-emission.json']=(json.dumps(dict(cuts=pins,
    status='INTERPRETED_GUARD_ONLY_LIBRARY_ADMISSION_OPEN',
    scope='Exact successful Guard and push declarations from a failed whole-library emission. Concrete Option/checked primitives require separate source admission. No failed declaration or generated axiom template is imported.'),indent=2)+'\n').encode()
for path,data in outputs.items():
    if args.check:assert path.read_bytes()==data,str(path)
    else:path.parent.mkdir(parents=True,exist_ok=True);path.write_bytes(data)
print(json.dumps(dict(check=args.check,selected_declarations=2)))
