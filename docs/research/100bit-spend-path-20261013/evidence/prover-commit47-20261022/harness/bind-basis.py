"""Reuse only byte-identical extracted arithmetic declaration bodies."""
from pathlib import Path
import re,json,hashlib
E=Path(__file__).resolve().parent.parent
L=Path('docs/research/v8-r0-zk-20261009/lean')
source=E/'extraction/basis-owner/Funs.lean'
retained=L/'AspisR1ProducerRelease47/Funs.lean'
def declarations(p):
 s=p.read_text();out={}
 for m in re.finditer(r'^def (\S+)',s,re.M):
  end=s.find('/--',m.start())
  if end<0:end=s.index('\nend ',m.start())
  out[m[1]]=s[m.start():end].strip()
 return out
old,new=declarations(retained),declarations(source)
reuse=[]
for k,v in new.items():
 if k.startswith('field.') and k not in ['field.QM31.ONE','field.wide_exact.WideExact.ONE','field.wide_exact.WideExact.sub']:
  assert v==old[k],k
  reuse.append(k)
extra=['field.QM31.ONE','field.wide_exact.WideExact.ONE','field.wide_exact.WideExact.sub','fill','stages','values']
text='''import AspisR1ProducerRelease47.Funs
/-! Extracted counter owner, with identical arithmetic callees rebound to the
previously proved release extraction. bind-counter.py checks every reused
callee declaration body byte-for-byte. No external template is installed. -/
open Aeneas Aeneas.Std Result ControlFlow Error
noncomputable section
namespace AspisR1ProducerRelease47
'''
for name in extra:
 if name.endswith('ONE'):text+='@[global_simps, irreducible]\n'
 text+=new[name]+'\n\n'
text+='end AspisR1ProducerRelease47\n'
p=L/'AspisR1ProducerRelease47/Basis.lean';p.write_text(text)
(E/'pins/basis-owner-callee-binding.json').write_text(json.dumps(dict(input_sha256=hashlib.sha256(source.read_bytes()).hexdigest(),retained_sha256=hashlib.sha256(retained.read_bytes()).hexdigest(),output_sha256=hashlib.sha256(p.read_bytes()).hexdigest(),reused_identical_declarations=reuse,selected_exact_declarations=extra),indent=2)+'\n')
