from pathlib import Path
E=Path(__file__).resolve().parent
s=(E/'NFP_UnsplitTrace.lean.txt').read_text()
a=s.index('def run ')
types=s[:a].replace('namespace AspisR1.NFP_QueryTrace','namespace AspisR1.NFP_TraceTypes')
types+='''theorem pure_result {T : Type} (x : T) : ((pure x : M T)).result=ok x := rfl
#print axioms pure_result
end AspisR1.NFP_TraceTypes
end
'''
(E/'NFP_TraceTypes.lean').write_text(types)
a=s.index('  let i ← eval');b=s.index('  let i1 ← eval',a);c=s.index('  if bad then',b);d=s.index('   let we6 ←',c);e=s.index('\n\n/-- Full',d)
head=s[a:b]+'  pure (u,q,dots)\n'
front=s[b:c]+'  pure (inverse,folded,values,bad)\n'
back=s[d:e]
for name,args,result,body,model in [
 ('Head','(proof : Slice U8) (p : verifier.Prepared) (a : verifier.Accumulator) (g : Array E 29#usize)','(Usize × Slice U8 × Dots)',head,'NFP_QueryCuts.head (NFP_ObserverErasure.erase base) proof p a g'),
 ('Front','(p : verifier.Prepared) (a : verifier.Accumulator) (geometry : verifier.QueryGeometry) (u : Usize) (q : Slice U8) (dots : Dots)','(Inverse × E × Dots × Bool)',front,'NFP_SuffixCuts.front (NFP_ObserverErasure.erase base) p a geometry u q dots'),
 ('Back','(p : verifier.Prepared) (a : verifier.Accumulator) (geometry : verifier.QueryGeometry) (pending : verifier.BatchedWeights) (inverse : Inverse) (values : Dots)','Out',back,'NFP_SuffixCuts.back (NFP_ObserverErasure.erase base) p a geometry pending inverse values')]:
 # Back is extracted from the branch, so shift its indentation one column.
 if name=='Back':body='\n'.join(l[1:] if l.startswith(' ') else l for l in body.splitlines())+'\n'
 applied={'Head':'proof p a g','Front':'p a geometry u q dots','Back':'p a geometry pending inverse values'}[name]
 source=f'''import NFP_TraceTypes
set_option autoImplicit false
noncomputable section
namespace AspisR1.NFP_Trace{name}
open Aeneas Aeneas.Std Result AspisR1Stage2 NFP_QueryCuts NFP_TraceTypes
open Port3_NativeQueryBody

def run (base : Ops) {args} : M {result} :=
 let ops := NFP_ObserverErasure.erase base
 do
'''+body+f'''
theorem erased (base : Ops) {args} :
 (run base {applied}).result = {model} := by
 simp only [run,eval,mark,NFI_TraceResult.erase_bind,NFI_TraceResult.erase_lift,
  NFI_TraceResult.erase_mark,pure_result,bind_tc_ok,
  NFP_QueryCuts.head,NFP_SuffixCuts.front,NFP_SuffixCuts.back] <;> rfl
#print axioms erased
end AspisR1.NFP_Trace{name}
end
'''
 (E/f'NFP_Trace{name}.lean').write_text(source)
# The final trace preserves all three native cuts and the rejected prefix.
(E/'NFP_QueryTrace.lean').write_text('''import NFP_TraceHead
import NFP_TraceFront
import NFP_TraceBack
set_option autoImplicit false
noncomputable section
namespace AspisR1.NFP_QueryTrace
open Aeneas Aeneas.Std Result AspisR1Stage2 NFP_QueryCuts NFP_TraceTypes
open Port3_NativeQueryBody

def run (base : Ops) (proof : Slice U8) (p : verifier.Prepared)
 (a : verifier.Accumulator) (g : Array E 29#usize)
 (geometry : verifier.QueryGeometry) (pending : verifier.BatchedWeights) : M Out := do
 let (u,q,dots) ← NFP_TraceHead.run base proof p a g
 let (inverse,_,values,bad) ← NFP_TraceFront.run base p a geometry u q dots
 if bad then pure (.Err verifier.Error.Query)
 else NFP_TraceBack.run base p a geometry pending inverse values

theorem erased (ops : Ops) (proof : Slice U8) (p : verifier.Prepared)
 (a : verifier.Accumulator) (g : Array E 29#usize)
 (geometry : verifier.QueryGeometry) (pending : verifier.BatchedWeights) :
 (run ops proof p a g geometry pending).result =
 verifier.candidate.query_values (NFP_ObserverErasure.erase ops) proof p a g none geometry pending := by
 rw [NFP_QueryCuts.source]
 simp only [run,NFI_TraceResult.erase_bind,NFP_TraceHead.erased,NFP_TraceFront.erased,
  apply_ite,NFP_TraceBack.erased,pure_result,NFP_SuffixCuts.source] <;> rfl
#print axioms erased
end AspisR1.NFP_QueryTrace
end
''')
