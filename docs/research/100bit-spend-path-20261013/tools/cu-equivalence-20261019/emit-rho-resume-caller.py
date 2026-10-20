#!/usr/bin/env python3
from pathlib import Path
import argparse
ap=argparse.ArgumentParser();ap.add_argument('--check',action='store_true');args=ap.parse_args()
tool=Path(__file__).resolve().parent;p=tool.parents[1];raw=tool/'rho-resume-caller-generated';out=p/'lean/AspisR1RhoResumeCaller'
def emit(n,text):
 if args.check:assert (out/n).read_text()==text,n
 else:out.mkdir(exist_ok=True);(out/n).write_text(text)
t='import AspisR1RhoStage.Types\nimport AspisR1RhoReader.Types\nopen Aeneas Aeneas.Std\nnamespace AspisR1RhoResumeCaller\n'
for n in ['aspis_core.field.M31','aspis_core.field.CM31','aspis_core.field.QM31','aspis_core.field.WideExact','aspis_core.circle.SecureCirclePoint','aspis_core.Digest32','transport.Variant','verifier.Error','verifier.Prepared','verifier.Accumulator']:t+='abbrev '+n+' := AspisR1RhoQuery.'+n+'\n'
t+='abbrev ResumeReader := AspisR1CuRho.verifier.Reader\n'
s=(raw/'Types.lean').read_text();t+=s[s.index('structure ResumeBegin'):s.index('end AspisR1RhoResumeCaller')]+'\nend AspisR1RhoResumeCaller\n';emit('Types.lean',t)
f=(raw/'Funs.lean').read_text().replace('namespace AspisR1RhoResumeCaller\n','namespace AspisR1RhoResumeCaller\nvariable [ResumeCommon]\n',1);emit('Funs.lean',f)
print("Exact resume-caller emitted bodies and source carrier aliases checked")
