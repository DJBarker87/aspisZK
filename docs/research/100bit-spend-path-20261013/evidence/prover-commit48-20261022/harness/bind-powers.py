"""Reuse only byte-identical extracted arithmetic declaration bodies."""
from pathlib import Path
import re,json,hashlib
E=Path(__file__).resolve().parent.parent
L=Path('docs/research/v8-r0-zk-20261009/lean')
source=E/'extraction/powers-owner/AspisR1PowersOwner48/Funs.lean'
retained=L/'AspisR1ProducerRelease47/Funs.lean'
def declarations(p):
 s=p.read_text();out={}
 matches=list(re.finditer(r'^def (\S+)',s,re.M))
 for i,m in enumerate(matches):
  end=matches[i+1].start() if i+1<len(matches) else s.index('\nend ',m.start())
  body=s[m.start():end].split('/--')[0].split('@[')[0].strip()
  out[m[1]]=body
 return out
old=declarations(retained)
old.update(declarations(L/'AspisR1ProducerRelease47/Pairs.lean'))
old.update(declarations(L/'AspisR1ProducerRelease47/Basis.lean'))
new=declarations(source)
reuse=[]
for k,v in new.items():
 if k.startswith('field.'):
  assert v==old[k],k
  reuse.append(k)
extra=['fill','gamma','kappa']
text='''import AspisR1ProducerRelease47.Basis
import AspisR1ProducerRelease47.Pairs
/-! Extracted counter owner, with identical arithmetic callees rebound to the
previously proved release extraction. bind-counter.py checks every reused
callee declaration body byte-for-byte. No external template is installed. -/
open Aeneas Aeneas.Std Result ControlFlow Error
noncomputable section
namespace AspisR1ProducerRelease47
'''
for name in extra:
 if name.endswith('ZERO'):text+='@[global_simps, irreducible]\n'
 text+=re.sub(r'\bfill\b','power_fill',new[name])+'\n\n'
text+='end AspisR1ProducerRelease47\n'
p=L/'AspisR1ProducerRelease47/Powers48.lean';p.write_text(text)
(E/'pins/powers-callee-binding.json').write_text(json.dumps(dict(input_sha256=hashlib.sha256(source.read_bytes()).hexdigest(),retained_sha256=hashlib.sha256(retained.read_bytes()).hexdigest(),output_sha256=hashlib.sha256(p.read_bytes()).hexdigest(),reused_identical_declarations=reuse,selected_exact_declarations=extra),indent=2)+'\n')
