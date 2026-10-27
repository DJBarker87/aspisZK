"""Bind the predecessor's original control representation to extracted primitives.
This is a structural source representation, not a new extractor emission.
"""
from pathlib import Path
import subprocess,hashlib,json
E=Path('evidence/pv-batch1-20261027');path='docs/research/v8-r0-zk-20261009/lean/R1Z/ProverRwP6PowersSource.lean'
rev='c57a344726745387efb38d1571d885c69ce829ee';old=subprocess.check_output(['git','show',rev+':'+path],text=True)
body=old[old.index('/-- [aspis_r1_cost_probe::weights::powers]'):old.rindex('end R1Z.ProverRwP6PowersSource')]
header='''-- Original early-return control from the pinned predecessor source representation.
-- Primitive bodies and constants are the actual freshly extracted CT operations.
import PV_B1_254_Funs
set_option autoImplicit false
noncomputable section
namespace PV_B1_PowersOriginal
open Aeneas Aeneas.Std Result ControlFlow Error
abbrev aspis_core.field.wide_exact.WideExact := PV_B1_254.aspis_core.field.wide_exact.WideExact
abbrev aspis_core.field.wide_exact.WideExact.mul := PV_B1_254.aspis_core.field.wide_exact.WideExact.mul
def aspis_core.field.wide_exact.WideExact.ZERO : Result aspis_core.field.wide_exact.WideExact :=
  ok PV_B1_254.aspis_core.field.wide_exact.WideExact.ZERO
def aspis_core.field.wide_exact.WideExact.ONE : Result aspis_core.field.wide_exact.WideExact :=
  ok PV_B1_254.aspis_core.field.wide_exact.WideExact.ONE
'''
footer='''#print axioms aspis_core.field.wide_exact.WideExact.ZERO
#print axioms aspis_core.field.wide_exact.WideExact.ONE
#print axioms aspis_core.field.wide_exact.WideExact.mul
#print axioms weights.powers_loop.body
#print axioms weights.powers_loop
#print axioms weights.powers
end PV_B1_PowersOriginal
'''
s=header+body+footer;(E/'lean/PV_B1_PowersOriginal.lean').write_text(s)
rust=Path('crates/aspis-r1-cost-probe/src/weights.rs').read_bytes();assert rust==subprocess.check_output(['git','show',rev+':crates/aspis-r1-cost-probe/src/weights.rs'])
(E/'powers-original-binding.json').write_text(json.dumps(dict(revision=rev,predecessor_representation=path,predecessor_source_sha256=hashlib.sha256(old.encode()).hexdigest(),rust_path='crates/aspis-r1-cost-probe/src/weights.rs',rust_sha256=hashlib.sha256(rust).hexdigest(),representation_sha256=hashlib.sha256(s.encode()).hexdigest(),control_body_verbatim=True,adaptations=['namespace/import only','bind WideExact carrier and mul directly to fresh extraction','bind ZERO/ONE to ok of fresh extracted constants'],boundary='structural source representation; not claimed as fresh extraction of the unsupported original early-return function'),indent=2)+'\n')
