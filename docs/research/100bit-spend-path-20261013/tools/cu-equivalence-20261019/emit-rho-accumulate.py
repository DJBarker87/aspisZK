#!/usr/bin/env python3
"""Emit full factored accumulation callers with explicit identical carrier aliases."""
from pathlib import Path
import argparse,hashlib,json
ap=argparse.ArgumentParser();ap.add_argument('--check',action='store_true');a=ap.parse_args()
tool=Path(__file__).resolve().parent;lean=tool.parents[1]/'lean';raw=tool/'rho-accumulate-factored-generated'
s=(raw/'Types.lean').read_text();start=s.index('structure verifier.Prepared');end=s.index('/-- [aspis_r1_cu_gamma::BatchedWeights]');records=s[start:end]
types='''import AspisR1RhoReferenceLoop.Types
import AspisR1RhoPowerTail.Types
namespace AspisR1RhoAccumulate
open Aeneas Aeneas.Std
abbrev aspis_core.field.M31 := AspisR1CuRho.field.M31
abbrev aspis_core.field.CM31 := AspisR1CuRho.field.CM31
abbrev aspis_core.field.QM31 := AspisR1CuRho.field.QM31
abbrev aspis_core.field.WideExact := AspisR1CuRho.field.WideExact
abbrev transport.Variant := AspisR1RhoPowerTail.transport.Variant
structure aspis_core.circle.SecureCirclePoint where
  x : aspis_core.field.QM31
  y : aspis_core.field.QM31
abbrev BatchedWeights := AspisR1CuRho.verifier.BatchedWeights
'''+records+'\nend AspisR1RhoAccumulate\n'
s=(raw/'Funs.lean').read_text();assert 'fail panic' not in s
funs=s.replace('namespace AspisR1RhoAccumulate\n','namespace AspisR1RhoAccumulate\nvariable [AccumulateCommon]\n',1)
assert funs.replace('variable [AccumulateCommon]\n','',1)==s
outputs={'AspisR1RhoAccumulate/Types.lean':types,'AspisR1RhoAccumulate/Funs.lean':funs}
for n,s in outputs.items():
 p=lean/n
 if a.check:assert p.read_text()==s,n
 else:p.parent.mkdir(exist_ok=True,parents=True);p.write_text(s)
print(json.dumps({'check':a.check,'function_body_changes':0,'outputs':{n:hashlib.sha256(s.encode()).hexdigest() for n,s in outputs.items()}}))
