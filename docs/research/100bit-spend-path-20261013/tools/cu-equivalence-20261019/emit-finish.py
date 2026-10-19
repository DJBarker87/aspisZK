#!/usr/bin/env python3
"""Promote exact emitted finish declarations with the mutable runtime import."""
from pathlib import Path
import argparse, hashlib, json

ap=argparse.ArgumentParser();ap.add_argument('--check',action='store_true');a=ap.parse_args()
here=Path(__file__).resolve().parent;area=here.parents[1]
source=here/'rho-generated/AspisR1CuRho/Funs.lean';raw=source.read_bytes()
sha=lambda b:hashlib.sha256(b).hexdigest()
assert sha(raw)=='f5a2b28be5e1dcbc1624dca905635473fb6e0724a44dd0800c818d30164394fa'
trait_start=raw.index(b'/-- Trait implementation:')
trait_end=raw.index(b'/-- [aspis_r1_cu_rho::field::P]')
finish_start=raw.index(b'/-- [aspis_r1_cu_rho::verifier::{aspis_r1_cu_rho::verifier::BatchedWeights}::finish]: loop body 0:')
finish_end=raw.index(b'end AspisR1CuRho',finish_start)
pieces=[('mutable_iterator_instance',trait_start,trait_end),('finish_cone',finish_start,finish_end)]
header=b'''-- Exact declaration slices from the full Aeneas emission; bodies unchanged.
import AspisR1CuRho.Funs
import AspisR1CuRho.MutableIteratorRuntime
open Aeneas Aeneas.Std Result ControlFlow Error
set_option linter.dupNamespace false
set_option linter.hashCommand false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000
set_option maxRecDepth 2048
noncomputable section
namespace AspisR1CuRho
'''
output=header+b'\n'.join(raw[start:end] for _,start,end in pieces)+b'end AspisR1CuRho\n'
manifest=dict(generated_input=str(source.relative_to(area)),generated_input_sha256=sha(raw),
    llbc_host_path='/home/dombarker/project-offloads/aspis-r1-cu-equivalence-20261019/Rho.llbc',
    llbc_sha256='3c911815301f0e01c88307325657634b4efd792058e843d99c9a05eca986dcb3',
    cuts=[dict(name=n,start_byte=s,end_byte_exclusive=e,sha256=sha(raw[s:e])) for n,s,e in pieces],
    output_sha256=sha(output),
    layout_changes=['Import already checked push/value source definitions and types',
        'Import namespace-local mutable Iterator interface instead of the incompatible ordinary interface',
        'Keep every selected emitted declaration byte-identical, including the generated trait instance'],
    scope='Emission promotion only. Mutable standard-library runtime source admission and finish execution/refinement proofs remain separate required obligations.')
dest=area/'lean/AspisR1CuRho/Finish.lean';pins=here/'finish-emission.json'
outputs={dest:output,pins:(json.dumps(manifest,indent=2)+'\n').encode()}
for path,data in outputs.items():
    if a.check:assert path.read_bytes()==data,str(path)
    else:path.write_bytes(data)
print(json.dumps(dict(check=a.check,output_sha256=sha(output),exact_declaration_cuts=len(pieces))))
