from pathlib import Path
import re,json,hashlib
E=Path(__file__).resolve().parent.parent
L=Path('docs/research/v8-r0-zk-20261009/lean/AspisR1ProducerRelease47')
source=E/'extraction/generic-owner/AspisR1Generic54/Funs.lean'
def declarations(p):
 s=re.sub(r'^(@\[[^\n]+\]) def ',r'\1\ndef ',p.read_text(),flags=re.M);out={}
 for m in re.finditer(r'^def (\S+)',s,re.M):
  ends=[x for x in [s.find('/--',m.end()),s.find('\ndef ',m.end()),s.find('\n@[',m.end()),s.find('\nend ',m.end())] if x>=0]
  out[m[1]]=s[m.start():min(ends)].strip()
 return out
old={};providers={}
# Only these imported modules may supply reused definitions.
imports=['Funs','Interpolate48','Basis','Opening48','Pairs','Samples49','Kernels49','EncoderNodes54']
for file in imports:
 p=L/(file+'.lean')
 for name,body in declarations(p).items():
  if name in old:assert body==old[name],name
  old[name]=body;providers[name]=str(p)
new=declarations(source);reuse=[]
for k,v in new.items():
 if k in old:
  assert v==old[k],('mismatched retained body',k)
  reuse.append(dict(name=k,provider=providers[k],sha256=hashlib.sha256(v.encode()).hexdigest()))
types=E/'extraction/generic-owner/AspisR1Generic54/Types.lean'
t=types.read_text();rt=(L/'Types.lean').read_text()
for name in ['field.M31','field.CM31','field.QM31']:
 def shape(s):
  m=re.search(r'^(?:def|structure) '+re.escape(name)+r'\b',s,re.M)
  end=min(x for x in [s.find('/--',m.end()),s.find('\nend ',m.end())] if x>=0)
  return s[m.start():end].strip()
 assert shape(t)==shape(rt),name
trait=t[t.index('structure scalar.CodeField'):t.index('\nend AspisR1Generic54')].strip()
selected={'generic54.collect','generic54.eval_rec','generic54.channels','generic54.phi_inverse','generic54.encode_with_nodes'}
for carrier in ['M31','CM31','QM31']:
 for method in ['from_m31','add','sub','mul']:
  name='field.'+carrier+'.Insts.Aspis_r1_encoder53ScalarCodeField.'+method
  if name in new:selected.add(name)
extra=[k for k in new if k not in old and k in selected]
text=''.join('import AspisR1ProducerRelease47.'+s+'\n' for s in imports)
text+='''/-! Exact generic owner extraction, including the native CodeField trait and
M31/QM31 used method bodies. Unused inverse records are excluded explicitly. All reused arithmetic and carrier shapes are
checked byte-for-byte by bind-generic.py. No external template is installed. -/
open Aeneas Aeneas.Std Result ControlFlow Error
noncomputable section
namespace AspisR1ProducerRelease47
'''+trait+'\n\n'
for k in extra:
 if k.endswith(('ZERO','ONE')):text+='@[global_simps, irreducible]\n'
 text+=new[k]+'\n\n'
text+='end AspisR1ProducerRelease47\n'
p=L/'EncoderGeneric54.lean';p.write_text(text)
(E/'encoder-generic-callee-binding.json').write_text(json.dumps(dict(input_sha256=hashlib.sha256(source.read_bytes()).hexdigest(),types_sha256=hashlib.sha256(types.read_bytes()).hexdigest(),output_sha256=hashlib.sha256(p.read_bytes()).hexdigest(),reused= reuse,selected_exact_declarations=extra,excluded_unused_declarations=[k for k in new if k not in old and k not in selected]),indent=2)+'\n')
print('exact new declarations',len(extra),'identical reused',len(reuse))
