from pathlib import Path
import re,json,hashlib,sys
E=Path(__file__).resolve().parent.parent;L=Path('docs/research/v8-r0-zk-20261009/lean')
new=(E/'extraction/fields29-v1-Funs.lean.txt').read_text();old=(L/'AspisR1SimSemantic20/Funs.lean').read_text()
def defs(s):
 out={}
 for m in re.finditer(r'^(?:def|impl_def) (\S+)\s',s,re.M):
  end=s.find('\n/--',m.end());end=end if end>=0 else s.index('\nend ',m.end())
  out[m[1]]=re.sub(r'\s+',' ',s[m.start():end]).strip()
 return out
n,o=defs(new),defs(old);root='r1_wire.fields29.finite'
diff=[k for k in n if k!=root and n[k]!=o.get(k)]
assert diff==[],diff
start=new.index('def '+root+'\n');body=new[start:new.index('\nend AspisR1FiniteFields29',start)]
text='''import AspisR1SimSemantic20.Funs
/-! Complete extracted fueled validator; all reused field dependencies have
identical bodies in the retained namespace. No opaque cut or template axiom. -/
namespace AspisR1SimSemantic20
open Aeneas Aeneas.Std Result
'''+body+'\nend AspisR1SimSemantic20\n'
p=L/'R1Z/ProverCommitFieldsSource29.lean'
if '--check' in sys.argv:assert p.read_text()==text
else:p.write_text(text)
(E/'fields-port.json').write_text(json.dumps(dict(reused_definitions=[k for k in n if k!=root],all_reused_bodies_match=True,namespace='AspisR1FiniteFields29 → AspisR1SimSemantic20',source_sha256=hashlib.sha256(new.encode()).hexdigest(),port_sha256=hashlib.sha256(text.encode()).hexdigest(),opaque_cut=False),indent=2)+'\n')
