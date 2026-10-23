"""Reuse only byte-identical extracted arithmetic declaration bodies."""
from pathlib import Path
import re,json,hashlib
E=Path(__file__).resolve().parent.parent
L=Path('docs/research/v8-r0-zk-20261009/lean')
source=E/'extraction/encoder-owner/AspisR1Encoder54/Funs.lean'
retained=L/'AspisR1ProducerRelease47/Funs.lean'
def declarations(p):
 s=re.sub(r'^(@\[[^\n]+\]) def ',r'\1\ndef ',p.read_text(),flags=re.M);out={}
 for m in re.finditer(r'^def (\S+)',s,re.M):
  ends=[x for x in [s.find('/--',m.end()),s.find('\ndef ',m.end()),s.find('\n@[',m.end()),s.find('\nend ',m.end())] if x>=0]
  end=min(ends)
  out[m[1]]=s[m.start():end].strip()
 return out
old,new=declarations(retained),declarations(source)
old.update(declarations(L/"AspisR1ProducerRelease47/Samples49.lean"))
old.update(declarations(L/"AspisR1ProducerRelease47/Basis.lean"))
old.update(declarations(L/"AspisR1ProducerRelease47/Interpolate48.lean"))
old.update(declarations(L/"AspisR1ProducerRelease47/Opening48.lean"))
old.update(declarations(L/"AspisR1ProducerRelease47/Pairs.lean"))
reuse=[]
for k,v in new.items():
 if k in old:
  assert v==old[k],(k,v,old[k])
  reuse.append(k)
extra=["encoder54.collect", "encoder54.eval_rec", "encoder54.channels"]
text='''import AspisR1ProducerRelease47.Samples49
import AspisR1ProducerRelease47.Basis
import AspisR1ProducerRelease47.Opening48
import AspisR1ProducerRelease47.Pairs
/-! Extracted explicit recursive encoder, with identical arithmetic callees rebound to the
previously proved release extraction. bind-encoder-phi.py checks every reused
callee declaration body byte-for-byte. No external template is installed. -/
open Aeneas Aeneas.Std Result ControlFlow Error
noncomputable section
namespace AspisR1ProducerRelease47
'''
for name in extra:
 if name.endswith(('ZERO','ONE')):text+='@[global_simps, irreducible]\n'
 text+=new[name]+'\n\n'
text+='end AspisR1ProducerRelease47\n'
p=L/'AspisR1ProducerRelease47/Encoder54.lean';p.write_text(text)
(E/'encoder-callee-binding.json').write_text(json.dumps(dict(input_sha256=hashlib.sha256(source.read_bytes()).hexdigest(),retained_sha256=hashlib.sha256(retained.read_bytes()).hexdigest(),output_sha256=hashlib.sha256(p.read_bytes()).hexdigest(),reused_identical_declarations=reuse,selected_exact_declarations=extra),indent=2)+'\n')
