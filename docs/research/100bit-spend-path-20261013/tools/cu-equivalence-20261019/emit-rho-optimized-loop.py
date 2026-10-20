#!/usr/bin/env python3
"""Specialize one concrete std method call using its complete source emission."""
from pathlib import Path
import argparse,hashlib,json
ap=argparse.ArgumentParser();ap.add_argument('--check',action='store_true');a=ap.parse_args()
tool=Path(__file__).resolve().parent;lean=tool.parents[1]/'lean'
raw=(tool/'rho-coefficients-generated/Funs.lean').read_text()
start=raw.index('/-- [aspis_r1_cu_gamma::rho_new::coefficients]: loop body')
raw=raw[start:raw.index('end AspisR1RhoCoefficients')]
old='core.option.Option.as_deref_mut (Mut0T.Insts.CoreOpsDerefDerefMut\n        BatchedWeights) pending'
new='AspisR1RhoSourceOption.source_reborrow pending'
assert raw.count(old)==1
specialized=raw.replace(old,new);assert specialized.replace(new,old)==raw
wrapper=(tool/'rho-source-option-input/lib.rs').read_text()
assert wrapper.split(' {')[-1].strip()=='value.as_deref_mut()}'
assert 'pending.as_deref_mut()' in (tool/'rho-coefficients-input/fragments/new-helper.rs').read_text()
outputs={
'AspisR1RhoSourceOption/Types.lean':'import AspisR1RhoReferenceLoop.Types\nnamespace AspisR1RhoSourceOption\nabbrev BatchedWeights := AspisR1RhoCoefficients.BatchedWeights\nend AspisR1RhoSourceOption\n',
'AspisR1RhoSourceOption/Funs.lean':(tool/'rho-source-option-generated/Funs.lean').read_text(),
'AspisR1RhoOptimizedLoop/FunsExternal.lean':'''import AspisR1RhoReferenceLoop.FunsExternal
import AspisR1RhoSourceOption.Funs
namespace AspisR1RhoCoefficients
abbrev BatchedWeights.push := AspisR1CuRho.verifier.BatchedWeights.push
end AspisR1RhoCoefficients
''',
'AspisR1RhoOptimizedLoop/Funs.lean':'''import AspisR1RhoOptimizedLoop.FunsExternal
open Aeneas Aeneas.Std Result ControlFlow Error
set_option linter.unusedVariables false
noncomputable section
namespace AspisR1RhoCoefficients
'''+specialized+'\nend AspisR1RhoCoefficients\n'}
for n,s in outputs.items():
 p=lean/n
 if a.check:assert p.read_text()==s,n
 else:p.parent.mkdir(exist_ok=True,parents=True);p.write_text(s)
print(json.dumps({'check':a.check,'call_specializations':1,'manual_function_body_replacement':False,'source_wrapper_expression':'value.as_deref_mut()','outputs':{n:hashlib.sha256(s.encode()).hexdigest() for n,s in outputs.items()}}))
