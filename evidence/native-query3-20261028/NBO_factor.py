from pathlib import Path
root=Path(__file__).resolve().parents[2];d=root/'docs/research/100bit-spend-path-20261013/lean'
s=(d/'Port3_NativeQueryBody.lean').read_text();a=s.index('  let i ← Array.index_usize p.queries a.next',s.index('def verifier.candidate.query_values (ops'))
b=s.index('  if b\n',a);c=s.index('    let we6 ←',b);e=s.index('\n\n/--',c)
pref=s[a:b];suff=s[c:e]
pref=pref.replace('a.next','next')
suff='\n'.join(line[2:] for line in suff.splitlines())
head='''import NBO_Enumerate
open Aeneas Aeneas.Std Result
set_option autoImplicit false
noncomputable section
namespace NBO_QueryFactor
open AspisR1 AspisR1Stage2 Port3_NativeQueryBody
abbrev Cut := Stage2E × Array Stage2E 4#usize × Array U32 5#usize
/-- Exact emitted prefix; only a.next is projected before entering. -/
def prefix (ops : Ops) (proof : Slice U8) (p : verifier.Prepared) (next : Usize)
 (g : Array Stage2E 29#usize) (geometry : verifier.QueryGeometry) :
 Result (core.result.Result Cut verifier.Error) := do
'''
mid='''  if b then ok (.Err verifier.Error.Query)
  else ok (.Ok (folded,values,inverse))
/-- Exact emitted accepted continuation, including the actual accumulation
body and mark. No child output is supplied independently. -/
def suffix (ops : Ops) (p : verifier.Prepared) (a : verifier.Accumulator)
 (obs : Option (verifier.Phase → Result Unit)) (geometry : verifier.QueryGeometry)
 (pending : verifier.BatchedWeights) (values : Array Stage2E 4#usize)
 (inverse : Array U32 5#usize) :
 Result (core.result.Result (verifier.Accumulator × verifier.BatchedWeights) verifier.Error) := do
'''
tail='''
private theorem associate {A B C : Type} (x : Result A) (f : A → Result B)
 (g : B → Result C) : ((x >>= f) >>= g) = (x >>= fun a => f a >>= g) := by
 cases x <;> rfl
private theorem branch {A B : Type} (b : Bool) (x y : Result A) (f : A → Result B) :
 ((if b then x else y) >>= f) = (if b then x >>= f else y >>= f) := by
 cases b <;> rfl
/-- Total Result equality, including rejected prefixes and divergence.
It factors the actual emitted function, not a selected successful output. -/
theorem association (ops : Ops) (proof : Slice U8) (p : verifier.Prepared)
 (a : verifier.Accumulator) (g : Array Stage2E 29#usize)
 (obs : Option (verifier.Phase → Result Unit)) (geometry : verifier.QueryGeometry)
 (pending : verifier.BatchedWeights) :
 verifier.candidate.query_values ops proof p a g obs geometry pending =
 (do let cut ← prefix ops proof p a.next g geometry
     match cut with
     | .Err error => ok (.Err error)
     | .Ok (_,values,inverse) => suffix ops p a obs geometry pending values inverse) := by
 unfold verifier.candidate.query_values prefix suffix
 simp only [associate,branch,bind_tc_ok]
#print axioms associate
#print axioms branch
#print axioms association
end NBO_QueryFactor
end
'''
(d/'NBO_QueryFactor.lean').write_text(head+pref+mid+suff+tail)
