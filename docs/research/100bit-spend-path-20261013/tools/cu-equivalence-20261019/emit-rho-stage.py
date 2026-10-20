#!/usr/bin/env python3
from pathlib import Path
import argparse
ap=argparse.ArgumentParser();ap.add_argument('--check',action='store_true');args=ap.parse_args()
tool=Path(__file__).resolve().parent;p=tool.parents[1];raw=tool/'rho-stage-context-generated';out=p/'lean/AspisR1RhoStage'
def emit(n,text):
 if args.check:assert (out/n).read_text()==text,n
 else:out.mkdir(exist_ok=True);(out/n).write_text(text)
t='import AspisR1RhoQuery.Types\nnamespace AspisR1RhoStage\n'
for n in ['aspis_core.field.M31','aspis_core.field.CM31','aspis_core.field.QM31','aspis_core.field.WideExact','aspis_core.circle.SecureCirclePoint','aspis_core.Digest32','transport.Variant','verifier.Error','verifier.Phase','verifier.View','verifier.Prepared','verifier.Accumulator','BatchedWeights','QueryGeometry']:t+='abbrev '+n+' := AspisR1RhoQuery.'+n+'\n'
t+='end AspisR1RhoStage\n';emit('Types.lean',t)
f=(raw/'Funs.lean').read_text().replace('namespace AspisR1RhoStage\n','namespace AspisR1RhoStage\nvariable [AspisR1RhoAccumulate.AccumulateCommon] [AspisR1RhoQuery.QueryCommon] [AspisR1CuRho.HeapReserve]\n',1);emit('Funs.lean',f)
print("Exact stage bodies and identical source carrier aliases checked")
