#!/usr/bin/env python3
from pathlib import Path
import hashlib,json,re
R=Path(__file__).resolve().parents[2];E=R/'evidence/port4c-20261023';L=R/'docs/research/100bit-spend-path-20261013/lean'
f=(E/'current-prefix/Funs.lean').read_text();body=f[f.index('/-- [aspis_r1_cost_probe::verifier::batch_prefix_products]'):f.index('\nend Port4C_Prefix')]
body=body.replace('aspis_core.field.M31.mul','ops.mul').replace('aspis_core.field.M31.ONE','ops.one')
names=re.findall(r'^def\s+([A-Za-z0-9_.]+)',body,re.M)
for n in sorted(names,key=len,reverse=True):
 body=re.sub(r'(?<![A-Za-z0-9_.])'+re.escape(n)+r'(?![A-Za-z0-9_.])','('+n+' ops)',body)
 body=body.replace('def ('+n+' ops)','def '+n+' (ops : Leaves)')
s='''import Port4C_GeometryFields
set_option autoImplicit false
noncomputable section
namespace AspisR1.Port4C_NativePrefix
open Aeneas Aeneas.Std Result ControlFlow Error AspisR1Stage2
structure Leaves where
  mul : U32 → U32 → Result U32
  one : Result U32

'''+body+'\n'+''.join('#print axioms '+n+'\n' for n in names)+'end AspisR1.Port4C_NativePrefix\nend\n'
out=L/'Port4C_NativePrefix.lean';out.write_text(s)
(E/'prefix-emission.json').write_text(json.dumps({'generated_source_sha256':hashlib.sha256(f.encode()).hexdigest(),'module_sha256':hashlib.sha256(s.encode()).hexdigest(),'native_rust_sha256':hashlib.sha256((R/'crates/aspis-r1-cost-probe/src/verifier.rs').read_bytes()).hexdigest(),'declarations':names,'normalizations':['namespace to job prefix','inherited transparent M31 U32 carrier','two primitive Leaves arguments; no external template imported'],'native_source_span':[134,145],'qualification':'Focused current MIR extraction; one and multiply interpretation are explicit primitive session A dependencies'},indent=2)+'\n')
