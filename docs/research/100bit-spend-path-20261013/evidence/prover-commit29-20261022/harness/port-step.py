"""Check every reused body and preserve the extracted step body mechanically."""
from pathlib import Path
import re,json,hashlib,sys
E=Path(__file__).resolve().parent.parent
L=Path('docs/research/v8-r0-zk-20261009/lean')
source=E/'extraction/iteration-v1-Funs.lean.txt'
new=source.read_text()
old=(L/'AspisR1SimSemantic20/Funs.lean').read_text()
def defs(s):
 out={}
 for m in re.finditer(r'^def (\S+)\s',s,re.M):
  end=s.find('\n/--',m.end());end=end if end>=0 else s.index('\nend ',m.end())
  out[m[1]]=re.sub(r'\s+',' ',s[m.start():end]).strip()
 return out
n,o=defs(new),defs(old)
# Compatibility port for the pinned library's U32 shift-count signature.
# Raw i32 annotation is ill-typed there. shift_count audits numeral equality.
diff=[k for k in n if k not in ['sim.owned29.semantic_step','sim.owned29.iteration'] and n[k]!=o.get(k)]
assert diff==['sampler.qm31_div_pass_loop.body']
assert n[diff[0]].replace('32#i32','32#u32')==o[diff[0]]
a=new.index('def sim.owned29.semantic_step\n');body=new[a:new.index('\nend AspisR1SemanticStep29',a)]
body=body.replace('verifier.Error','AspisR1SimControl21.verifier.Error')
text='''import AspisR1SimSemantic20.Funs
import AspisR1SimControl21.Types
/-! Extracted one-step owner. All extracted semantic dependencies match the
retained namespace; only the verifier Error type is identified nominally. -/
set_option autoImplicit false
namespace AspisR1SimSemantic20
open Aeneas Aeneas.Std Result
'''+body+'\nend AspisR1SimSemantic20\n'
p=L/'R1Z/ProverCommitStepSource29.lean'
if '--check' in sys.argv:assert p.read_text()==text
else:p.write_text(text)
(E/'step-port.json').write_text(json.dumps(dict(reused_definitions=[k for k in n if k not in ['sim.owned29.semantic_step','sim.owned29.iteration']],all_reused_bodies_match_after_shift_annotation=True,shift_compatibility={'definition':diff[0],'raw':'32#i32','retained':'32#u32','audit':'R1Z.ProverCommitStep29.shift_count'},namespace='AspisR1SemanticStep29 → AspisR1SimSemantic20',verifier_type='AspisR1SimControl21.verifier.Error',source_sha256=hashlib.sha256(new.encode()).hexdigest(),port_sha256=hashlib.sha256(text.encode()).hexdigest()),indent=2)+'\n')
