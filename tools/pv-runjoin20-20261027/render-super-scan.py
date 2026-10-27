from pathlib import Path
import sys
L=Path(__file__).resolve().parents[2]/'docs/research/v8-r0-zk-20261009/lean/R1Z'
s='''import R1Z.PV_RunJoin_CompilerChecks17
set_option autoImplicit false
namespace R1Z.PV_RunJoin_SuperScan20
open Aeneas Aeneas.Std Result
open BuilderForestAdmissionPort
open BuilderForestAdmissionPort.pool_v1
abbrev WordArray := Array U32 8#usize
abbrev Outer := core.slice.iter.Iter WordArray
abbrev Inner := core.slice.iter.Iter U32
abbrev Flat := BuilderForestStd.Flatten Outer WordArray U32 Inner
abbrev outerIt := core.iter.traits.iterator.IteratorSliceIter WordArray
abbrev innerIt := core.iter.traits.iterator.IteratorSliceIter U32
abbrev convert := SharedArray.Insts.CoreIterTraitsCollectIntoIteratorSharedIter U32 8#usize
abbrev iterator : core.iter.traits.iterator.Iterator Flat U32 :=
  BuilderForestStdPort.core.iter.adapters.flatten.Flatten.Insts.CoreIterTraitsIteratorIterator outerIt convert innerIt
abbrev predicate := pair_forest_trace.compile_forest_from_copies.closure.Insts.CoreOpsFunctionFnMutTupleSharedM31Bool
abbrev input := PV_RunJoin_FixtureArguments.witness.super_root_siblings

def initial : Flat := ⟨⟨Array.to_slice input,0⟩,none⟩
def state (k : Nat) : Flat := if k=0 then initial else
  ⟨⟨Array.to_slice input,(k-1)/8+1⟩,some ⟨Array.to_slice input.val[(k-1)/8]!, (k-1)%8+1⟩⟩
def final : Flat := ⟨⟨Array.to_slice input,3⟩,none⟩
def word (k : Nat) : U32 := input.val[k/8]!.val[k%8]!
'''
s+='def outer (i : Nat) : Outer := ⟨Array.to_slice input,i⟩\ndef inner (b i : Nat) : Inner := ⟨Array.to_slice input.val[b]!,i⟩\n'
for k in range(24):
 b=k//8;i=k%8
 start='⟨outer 0,none⟩' if k==0 else f'⟨outer {b},some (inner {b-1} 8)⟩' if i==0 else f'⟨outer {b+1},some (inner {b} {i})⟩'
 s+=f"theorem next{k} : iterator.next (state {k}) = ok (some (word {k}),state {k+1}) := by\n"
 s+=f'  change BuilderForestStd.flattenNext outerIt convert innerIt {start} = ok (some (word {k}),⟨outer {b+1},some (inner {b} {i+1})⟩)\n'
 if k and i==0:
  s+=f'  rw [BuilderForestStd.flattenNext_skip outerIt convert innerIt (outer {b}) (inner {b-1} 8) (inner {b-1} 8) (by with_unfolding_all rfl)]\n'
 if i==0:
  s+=f'  rw [BuilderForestStd.flattenNext_open outerIt convert innerIt (outer {b}) (outer {b+1}) input.val[{b}]! (inner {b} 0) (by with_unfolding_all rfl) (by with_unfolding_all rfl)]\n'
 s+=f'  exact BuilderForestStd.flattenNext_yield outerIt convert innerIt (outer {b+1}) (inner {b} {i}) (inner {b} {i+1}) (word {k}) (by with_unfolding_all rfl)\n#print axioms next{k}\n'
 s+=f"""theorem predicate{k} : pair_forest_trace.compile_forest_from_copies.closure.Insts.CoreOpsFunctionFnMutTupleSharedM31Bool.call_mut () (word {k}) = ok (false,()) := by
  with_unfolding_all rfl
#print axioms predicate{k}
"""
s+='''theorem done : iterator.next (state 24) = ok (none,final) := by
  change BuilderForestStd.flattenNext outerIt convert innerIt ⟨outer 3,some (inner 2 8)⟩ = ok (none,⟨outer 3,none⟩)
  rw [BuilderForestStd.flattenNext_skip outerIt convert innerIt (outer 3) (inner 2 8) (inner 2 8) (by with_unfolding_all rfl)]
  exact BuilderForestStd.flattenNext_done outerIt convert innerIt (outer 3) (outer 3) (by with_unfolding_all rfl)
#print axioms done

theorem source : BuilderForestStd.iterAny iterator predicate initial () = ok (false,final) := by
  change BuilderForestStd.iterAny iterator predicate (state 0) () = _
'''
for k in range(24):s+=f'''  rw [BuilderForestStd.iterAny,next{k}]
  simp only [bind_tc_ok]
  rw [predicate{k}]
  simp only [bind_tc_ok,Bool.false_eq_true,if_false]
'''
s+='''  rw [BuilderForestStd.iterAny,done]
  rfl
#print axioms source
end R1Z.PV_RunJoin_SuperScan20
'''
p=L/'PV_RunJoin_SuperScan20.lean'
if '--check' in sys.argv:assert p.read_text()==s
else:p.write_text(s)
print('24 bounded iterator next and canonicality certificates')
