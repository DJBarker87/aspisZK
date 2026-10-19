#!/usr/bin/env python3
"""Select successful concrete NeverShortCircuit declarations, no dictionaries."""
from pathlib import Path
import argparse,hashlib,json
ap=argparse.ArgumentParser();ap.add_argument('--check',action='store_true');args=ap.parse_args()
here=Path(__file__).resolve().parent;area=here.parents[1];sha=lambda b:hashlib.sha256(b).hexdigest()
types=(here/'array-guard-generated/Types.lean').read_bytes()
funs=(here/'array-guard-generated/Funs.lean').read_bytes()
assert sha(types)=='f029e4a5ab88e0bc1f10a4d6f98d936cabea7f0b9daddae7ea9e22467261f345'
assert sha(funs)=='c54977eb154335a18e2b394257c6c49d74a63fe888b72a9454d7868951a6714c'
first=types.index(b'/-- [core::ops::try_trait::NeverShortCircuitResidual]')
last=types.index(b'/-- [core::array::Guard]')
type_cut=types[first:last]
start=funs.index(b'/-- [core::ops::try_trait::{impl core::ops::try_trait::FromResidual')
end=funs.index(b'/-- Trait implementation: [core::ops::try_trait::{impl core::ops::try_trait::Try')
operation_cut=funs[start:end]
assert b'sorry' not in type_cut+operation_cut and b'axiom ' not in type_cut+operation_cut
header=b'-- Exact successful emitted declaration cuts; bodies unchanged.\n'
header+=b'open Aeneas Aeneas.Std Result ControlFlow Error\nnamespace AspisR1CuArraySource\n'
out_types=b'import AspisR1CuArraySource.Types\n'+header+type_cut+b'end AspisR1CuArraySource\n'
out_ops=b'import AspisR1CuArraySource.NeverTypes\n'+header+operation_cut+b'end AspisR1CuArraySource\n'
outputs={area/'lean/AspisR1CuArraySource/NeverTypes.lean':out_types,
    area/'lean/AspisR1CuArraySource/NeverOperations.lean':out_ops,
    here/'never-short-circuit-emission.json':(json.dumps(dict(
        types=dict(input_sha256=sha(types),first=first,last=last,selected_sha256=sha(type_cut),output_sha256=sha(out_types)),
        operations=dict(input_sha256=sha(funs),first=start,last=end,selected_sha256=sha(operation_cut),output_sha256=sha(out_ops)),
        status='CONCRETE_METHODS_ONLY_GENERIC_DICTIONARY_ADMISSION_OPEN'),indent=2)+'\n').encode()}
for path,data in outputs.items():
    if args.check:assert path.read_bytes()==data,str(path)
    else:path.parent.mkdir(parents=True,exist_ok=True);path.write_bytes(data)
print(json.dumps(dict(check=args.check,method_bodies_unchanged=True)))
