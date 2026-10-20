#!/usr/bin/env python3
from pathlib import Path
import argparse
ap=argparse.ArgumentParser();ap.add_argument('--check',action='store_true');args=ap.parse_args()
tool=Path(__file__).resolve().parent;p=tool.parents[1];raw=tool/'rho-query-context-generated';out=p/'lean/AspisR1RhoQuery'
def emit(n,text):
 if args.check:assert (out/n).read_text()==text,n
 else:out.mkdir(exist_ok=True);(out/n).write_text(text)
s=(raw/'Types.lean').read_text()
def cut(a,b):return s[s.index(a):s.index(b)]
t='''import AspisR1RhoAccumulate.Types
namespace AspisR1RhoQuery
open Aeneas Aeneas.Std
abbrev aspis_core.field.M31 := AspisR1RhoAccumulate.aspis_core.field.M31
abbrev aspis_core.field.CM31 := AspisR1RhoAccumulate.aspis_core.field.CM31
abbrev aspis_core.field.QM31 := AspisR1RhoAccumulate.aspis_core.field.QM31
abbrev aspis_core.field.WideExact := AspisR1RhoAccumulate.aspis_core.field.WideExact
abbrev aspis_core.circle.SecureCirclePoint := AspisR1RhoAccumulate.aspis_core.circle.SecureCirclePoint
abbrev transport.Variant := AspisR1RhoAccumulate.transport.Variant
abbrev verifier.Prepared := AspisR1RhoAccumulate.verifier.Prepared
abbrev verifier.Accumulator := AspisR1RhoAccumulate.verifier.Accumulator
abbrev BatchedWeights := AspisR1RhoAccumulate.BatchedWeights
'''
t+=cut('structure aspis_core.Digest32','/-- [aspis_r1_cu_gamma::aspis_core::field::WideExact]')
t+=cut('@[discriminant isize]\ninductive verifier.Error','/-- [aspis_r1_cu_gamma::verifier::Prepared]')
t+=cut('structure QueryGeometry','end AspisR1RhoQuery')+'\nend AspisR1RhoQuery\n'
t=t.replace('@[discriminant isize]\ninductive verifier.Error','inductive verifier.Error').replace('@[discriminant isize]\ninductive verifier.Phase','inductive verifier.Phase')
emit('Types.lean',t)
f=(raw/'Funs.lean').read_text().replace('namespace AspisR1RhoQuery\n','namespace AspisR1RhoQuery\nvariable [AspisR1RhoAccumulate.AccumulateCommon] [QueryCommon]\n',1);emit('Funs.lean',f)
print("Exact query bodies and identical source carrier aliases checked")
