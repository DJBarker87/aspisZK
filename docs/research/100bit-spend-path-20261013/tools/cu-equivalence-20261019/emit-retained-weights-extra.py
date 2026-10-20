#!/usr/bin/env python3
from pathlib import Path
import argparse,re,json,hashlib
ap=argparse.ArgumentParser();ap.add_argument('--check',action='store_true');a=ap.parse_args();tool=Path(__file__).resolve().parent;area=tool.parents[1];lean=area/'lean';sha=lambda s:hashlib.sha256(s.encode()).hexdigest()
raw=(tool/'retained-weights-extra-generated/Funs.lean').read_text();s=raw[raw.index('/-- [aspis_r1_cu_canonical_dots::extra]'):raw.index('\nend AspisR1RetainedWeightsExtra')];body=s.replace('def extra\n','def retained.weights_extra\n').replace('field.QM31','aspis_core.field.QM31');assert body.replace('aspis_core.field.QM31','field.QM31').replace('def retained.weights_extra\n','def extra\n')==s
def decls(text):
 out={}
 for block in re.split(r'(?m)(?=^/--)',text)[1:]:
  m=re.search(r'(?m)^(?:structure|def) ([\w.]+)',block)
  if m:
   st=m.start();en=block.find('\n\n',st);out[m[1]]=block[st:en if en>=0 else None].split('\nend ')[0].strip()
 return out
rt=decls((tool/'retained-weights-extra-generated/Types.lean').read_text());pt=decls((lean/'AspisR1RhoPowerTail/Types.lean').read_text());shared=[]
for name,text in rt.items():
 n=name.replace('field.','aspis_core.field.',1);assert text.replace('field.','aspis_core.field.')==pt[n],n;shared.append(n)
text='import CuSavingsRetainedCompositionTx1Source\nopen Aeneas Aeneas.Std Result\nnamespace AspisR1RhoPowerTail\n'+body+'\n#print axioms retained.weights_extra\nend AspisR1RhoPowerTail\n'
meta=dict(raw_function_sha256=sha(s),shared_source_nominal_types=shared,inverse_source_body_checked=True,installed_source_sha256=sha(text))
for p,data in [(lean/'CuSavingsRetainedCompositionWeightsExtraSource.lean',text),(tool/'retained-weights-extra-emission.json',json.dumps(meta,indent=2)+'\n')]:
 if a.check:assert p.read_text()==data,p
 else:p.write_text(data)
print(json.dumps(dict(check=a.check,shared=len(shared),raw_function_body_unchanged=True)))
