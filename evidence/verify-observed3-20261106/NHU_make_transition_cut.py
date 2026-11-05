from pathlib import Path
import hashlib,json
E=Path(__file__).resolve().parent;R=E.parents[1]
s=(R/'lean/FIq_Native11.lean').read_text();start=s.index('  := do',s.index('def pool_v1.pair_forest_semantic_terminal.validate_transition_loop'))+len('  := ');end=s.index('\npartial_fixpoint',start);body=s[start:end]
import re
pat=r'pool_v1\.pair_forest_semantic_terminal\.validate_transition_loop\s+public1\s+(iter[12]) carry'
changed,count=re.subn(pat,lambda m:'next '+m[1],body);assert count==3
assert re.sub(r'next (iter[12])',lambda m:'pool_v1.pair_forest_semantic_terminal.validate_transition_loop public1 '+m[1]+' carry',changed).split()==body.split()
head='''import NHU_TransitionWords
set_option autoImplicit false
noncomputable section
open Aeneas Aeneas.Std Result
namespace AspisR1.NHU_TransitionCut
open FIq_Native
abbrev Public := pool_v1.pair_forest_semantic_terminal.SemanticPublic
abbrev RR := core.result.Result Unit pool_v1.pair_forest_semantic_terminal.PoolV1PairForestSemanticTerminalErrorV1
abbrev R := core.ops.range.Range Usize
def step (public1 : Public) (iter : R) (carry : Usize)
 (next : R→Result RR) : Result RR :=
'''
tail='''
theorem source (public1 : Public) (iter : R) (carry : Usize) :
 pool_v1.pair_forest_semantic_terminal.validate_transition_loop public1 iter carry=
 step public1 iter carry (fun next=>pool_v1.pair_forest_semantic_terminal.validate_transition_loop public1 next carry) := by
 rw [pool_v1.pair_forest_semantic_terminal.validate_transition_loop.eq_def]
 rfl
#print axioms source
end AspisR1.NHU_TransitionCut
end
'''
(E/'NHU_TransitionCut.lean').write_text(head+changed+tail)
(E/'NHU_TRANSITION_LEAN_ERASURE.json').write_text(json.dumps(dict(source='lean/FIq_Native11.lean',source_sha256=hashlib.sha256(s.encode()).hexdigest(),original_body_sha256=hashlib.sha256(body.encode()).hexdigest(),calls=count,method='exact emitted one-layer body; recursive calls replaced only by named continuation',status='PASS'),indent=1)+'\n')
