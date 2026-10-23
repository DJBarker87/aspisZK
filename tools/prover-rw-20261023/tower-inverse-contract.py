#!/usr/bin/env python3
"""Bind actual generic tower inverse control to the retained scalar algorithm."""
from pathlib import Path
import hashlib,json,os,subprocess
R=Path(__file__).resolve().parents[2];C=R/'tools/prover-rw-20261023/contracts'
p=R/'crates/aspis-core/src/r0/scalar.rs';s=p.read_text()
# Only the imported representation changes; all generic control is retained.
old=(C/'scalar-v2.rs.txt').read_text()
assert s==old,'The audited generic scalar algorithm changed'
(C/'reference_scalar.rs').write_text(old.replace('use crate::field::{WideExact, CM31, M31, P, QM31};','use super::reference_tower_field::{WideExact, CM31, M31, P, QM31};'))
scalar=(C/'reference_scalar.rs').read_text()
start=scalar.index('impl CodeField for M31 {');a=scalar.index('fn try_inv(',start);b=scalar.index('{',a);end=b+1;depth=1
while depth:
 depth+=(scalar[end]=='{')-(scalar[end]=='}');end+=1
(C/'tower-inverse-base-boundary.json').write_text(json.dumps(dict(original_body_sha256=hashlib.sha256(scalar[a:end].encode()).hexdigest(),supplied_contract='generic-inverse-kani-001: canonical M31 zero guard and 61 multiplication trace; source scalar.rs unchanged from its receipt',scope='Lower base inverse frame; canonical arbitrary answer for nonzero input, None at zero; no new inverse field law'),indent=2)+'\n')
(C/'reference_scalar.rs').write_text(scalar[:b]+'{super::tower_inverse_contracts::old_minv(self)}'+scalar[end:])
field=R/'tools/ct-kernels-20261022/reference/field.rs'
text=field.read_text();body_pins=[]
for ty,prefix in [('M31','rm'),('CM31','rc'),('QM31','rq')]:
 for op in ['add','sub','neg','mul']:
  start=text.index('impl '+ty+' {');at=text.index('pub fn '+op+'(',start);brace=text.index('{',at);end=brace+1;depth=1
  while depth:
   depth+=(text[end]=='{')-(text[end]=='}');end+=1
  original=text[at:end];body_pins.append(dict(type=ty,operation=op,original_sha256=hashlib.sha256(original.encode()).hexdigest(),replacement='Canonical parametric lower-kernel operation, same ordered trace as the actual selected CT arithmetic contract'))
  args='self' if op=='neg' else 'self, rhs'
  text=text[:brace]+'{super::tower_inverse_contracts::'+prefix+op+'('+args+')}'+text[end:]
text=text.replace('#[path = "field/wide_exact.rs"]','#[path = "../../ct-kernels-20261022/reference/field/wide_exact.rs"]')
(C/'reference_tower_field.rs').write_text(text)
(C/'tower-inverse-reference-boundaries.json').write_text(json.dumps(dict(reference_field_sha256=hashlib.sha256(field.read_bytes()).hexdigest(),adapted_sha256=hashlib.sha256(text.encode()).hexdigest(),boundaries=body_pins),indent=2)+'\n')
(C/'tower-inverse-bindings.json').write_text(json.dumps(dict(source=str(p.relative_to(R)),sha256=hashlib.sha256(p.read_bytes()).hexdigest(),reference_revision='084f714ccd',reference_scalar_sha256=hashlib.sha256(old.encode()).hexdigest(),adaptation='Generic scalar control is verbatim; its field import points to retained representations with lower elementary operations supplied by the checked CT contracts; exact replaced body pins in tower-inverse-reference-boundaries.json',domain='Canonical input limbs; lower M31/CM31/QM31 arithmetic supplied by previously checked CT contracts. Parametric ordered operation/operand/result and error equality, not a standalone inversion field-law proof.'),indent=2)+'\n')
cmd=['timeout','120','cargo','kani','--manifest-path','tools/prover-rw-20261023/contracts/Cargo.toml','--lib','--exact','--harness','tower_inverse_contracts::generic_tower_inverse_trace','--solver','kissat','--no-assertion-reach-checks','--output-format','terse','-j','1','-Z','unstable-options','-Z','stubbing','--cbmc-args','--unwinding-assertions']
subprocess.run(['python3',str(R/'tools/prover-rw-20261023/run-host.py'),'tower-inverse-kani-005',*cmd],env=dict(os.environ,CT_EXPECTED='Optimized Kani compile then generic C/Q/E inverse exact control/operand/result trace, canonical limbs; lower CT arithmetic contracts supplied; no nonlinear whole-field inversion bit-blast'),check=True)
