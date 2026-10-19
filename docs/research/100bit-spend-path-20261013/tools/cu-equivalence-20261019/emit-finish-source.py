#!/usr/bin/env python3
"""Interpret exact emitted finish declarations with the extracted std next."""
from pathlib import Path
import argparse,hashlib,json
ap=argparse.ArgumentParser();ap.add_argument('--check',action='store_true');a=ap.parse_args()
here=Path(__file__).resolve().parent;area=here.parents[1]
raw=(here/'rho-generated/AspisR1CuRho/Funs.lean').read_bytes()
sha=lambda b:hashlib.sha256(b).hexdigest()
assert sha(raw)=='f5a2b28be5e1dcbc1624dca905635473fb6e0724a44dd0800c818d30164394fa'
first=raw.index(b'/-- [aspis_r1_cu_rho::verifier::{aspis_r1_cu_rho::verifier::BatchedWeights}::finish]: loop body 0:')
last=raw.index(b'end AspisR1CuRho',first)
output=b'''-- Exact generated finish declarations, interpreted with extracted std next.
import AspisR1CuRhoSource.Runtime
open Aeneas Aeneas.Std Result ControlFlow Error
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000
set_option maxRecDepth 2048
noncomputable section
namespace AspisR1CuRhoSource
'''+raw[first:last]+b'end AspisR1CuRhoSource\n'
pins=dict(input_sha256=sha(raw),start=first,end=last,declaration_cut_sha256=sha(raw[first:last]),
 output_sha256=sha(output),
 layout_changes=['Namespace only; all three emitted finish declarations byte-identical',
  'Type/value aliases reuse the checked production rho carrier and value method',
  'Selected mutable next calls the unchanged emitted concrete standard method'],
 scope='Selected source interpretation. Consuming context theorem required; no generic Iterator replacement or whole-verifier claim.')
for path,data in {area/'lean/AspisR1CuRhoSource/Finish.lean':output,
 here/'finish-source-emission.json':(json.dumps(pins,indent=2)+'\n').encode()}.items():
 if a.check:assert path.read_bytes()==data,str(path)
 else:path.parent.mkdir(parents=True,exist_ok=True);path.write_bytes(data)
print(json.dumps(dict(check=a.check,output_sha256=sha(output))))
