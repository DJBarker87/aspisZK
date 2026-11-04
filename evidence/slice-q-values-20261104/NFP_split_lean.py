"""Factor the checked source tail without changing any primitive call."""
from pathlib import Path
E=Path(__file__).resolve().parent;s=(E/'NFP_QueryCuts.lean').read_text()
a=s.index('  let i1 ←',s.index('def tail'));b=s.index('  if b\n',a);c=s.index('    let we6 ←',b);d=s.index('\n\ntheorem source',c)
front=s[a:b];back=s[c:d]
header='''import NFP_QueryCuts
set_option autoImplicit false
noncomputable section
namespace AspisR1.NFP_SuffixCuts
open Aeneas Aeneas.Std Result AspisR1Stage2 NFP_QueryCuts
open Port3_NativeQueryBody
abbrev Inverse := Array aspis_core.field.M31 5#usize

def front (ops : Ops) (p : verifier.Prepared) (a : verifier.Accumulator)
 (geometry : verifier.QueryGeometry) (u : Usize) (q : Slice U8) (dots : Dots) :
 Result (Inverse × E × Dots × Bool) := do
'''
header+=front+'  ok (inverse,folded,values,b)\n\n'
header+='''def back (ops : Ops) (p : verifier.Prepared) (a : verifier.Accumulator)
 (geometry : verifier.QueryGeometry) (pending : verifier.BatchedWeights)
 (inverse : Inverse) (values : Dots) : Result Out := do
'''+back+'\n\n'
header+='''theorem source (ops : Ops) (p : verifier.Prepared) (a : verifier.Accumulator)
 (geometry : verifier.QueryGeometry) (pending : verifier.BatchedWeights)
 (u : Usize) (q : Slice U8) (dots : Dots) :
 tail ops p a geometry pending u q dots =
 (do let (inverse,_,values,b) ← front ops p a geometry u q dots
     if b then ok (.Err verifier.Error.Query)
     else back ops p a geometry pending inverse values) := by
 simp only [front,back,tail,bind_assoc_eq,bind_tc_ok] <;> rfl
#print axioms source
end AspisR1.NFP_SuffixCuts
end
'''
(E/'NFP_SuffixCuts.lean').write_text(header)
