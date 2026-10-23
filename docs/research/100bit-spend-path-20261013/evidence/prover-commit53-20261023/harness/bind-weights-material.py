"""Reuse only byte-identical extracted arithmetic declaration bodies."""
from pathlib import Path
import re,json,hashlib
E=Path(__file__).resolve().parent.parent
L=Path('docs/research/v8-r0-zk-20261009/lean')
source=E/'extraction/weights-material-owner/AspisR1WeightsMaterial53/Funs.lean'
retained=L/'AspisR1ProducerRelease47/Funs.lean'
def declarations(p):
 s=re.sub(r'^(@\[[^\n]+\]) def ',r'\1\ndef ',p.read_text(),flags=re.M);out={}
 for m in re.finditer(r'^def (\S+)',s,re.M):
  ends=[x for x in [s.find('/--',m.end()),s.find('\ndef ',m.end()),s.find('\n@[',m.end()),s.find('\nend ',m.end())] if x>=0]
  end=min(ends)
  out[m[1]]=s[m.start():end].strip()
 return out
old,new=declarations(retained),declarations(source)
old.update(declarations(L/"AspisR1ProducerRelease47/Basis.lean"))
old.update(declarations(L/"AspisR1ProducerRelease47/Interpolate48.lean"))
old.update(declarations(L/"AspisR1ProducerRelease47/Opening48.lean"))
old.update(declarations(L/"AspisR1ProducerRelease47/Pairs.lean"))
for p in sorted((L/"AspisR1ProducerRelease47").glob("*.lean")):
 if p.name!="WeightsMaterial53.lean":old.update(declarations(p))
old.update(declarations(L/"R1Z/ProverCommitInactiveSource49.lean"))
reuse=[]
for k,v in new.items():
 if k in old:
  compared=v.replace("owned.inactive","AspisR1InactiveOwner49.owned.inactive") if k=="weights53.raw" else v
  assert compared==old[k],(k,v,old[k])
  reuse.append(k)
extra=[k for k in new if k not in old]
text='''import AspisR1ProducerRelease47.Weights53
import AspisR1ProducerRelease47.Weights49
import AspisR1ProducerRelease47.PointRows49
import AspisR1ProducerRelease47.Points49
import AspisR1ProducerRelease47.Stored49
import AspisR1ProducerRelease47.KernelCallers49
import R1Z.ProverCommitInactiveSource49
/-! Extracted counter owner, with identical arithmetic callees rebound to the
previously proved release extraction. bind-counter.py checks every reused
callee declaration body byte-for-byte. No external template is installed. -/
open Aeneas Aeneas.Std Result ControlFlow Error
noncomputable section
namespace AspisR1ProducerRelease47
'''
for name in extra:
 if name.endswith(('ZERO','ONE')):text+='@[global_simps, irreducible]\n'
 text+=new[name].replace('owned.inactive','AspisR1InactiveOwner49.owned.inactive')+'\n\n'
text+='end AspisR1ProducerRelease47\n'
p=L/'AspisR1ProducerRelease47/WeightsMaterial53.lean';p.write_text(text)
(E/'weights-material-callee-binding.json').write_text(json.dumps(dict(input_sha256=hashlib.sha256(source.read_bytes()).hexdigest(),retained_sha256=hashlib.sha256(retained.read_bytes()).hexdigest(),output_sha256=hashlib.sha256(p.read_bytes()).hexdigest(),reused_identical_declarations=reuse,selected_exact_declarations=extra),indent=2)+'\n')
