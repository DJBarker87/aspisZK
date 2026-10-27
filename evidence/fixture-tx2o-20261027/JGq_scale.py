from pathlib import Path
import sys
R=Path(__file__).resolve().parents[2];x={'__file__':str(R/'evidence/fixture-tx2n-20261027/JGo_arithmetic.py')};exec((R/'evidence/fixture-tx2n-20261027/JGo_arithmetic.py').read_text().split('mods,results=generate()')[0],x)
P=2147483647;perm=[0,3,2,1];out={}
for tag in [0,1]:
 alpha=x['scalar']('JFq_Alpha'+str(tag));ap=[[1]+[0]*7]
 for _ in range(3):ap.append(x['mul'](ap[-1],alpha))
 row=x['nums']('JGo_TX2_WeightData',f'f0{tag}');vs=[[0]*8]
 for i in range(4):vs.append(x['add'](vs[-1],x['mul'](ap[perm[i]],row[4*i:4*i+4]+[0]*4)))
 final=[(v*pow(4,-1,P))%P for v in vs[4]]
 mod=f'JGq_Scale{tag}';s=f'''import JGq_Powers{tag}
import JGo_TX2_WeightData
import FJg_ScalarFold
set_option autoImplicit false
noncomputable section
namespace AspisR1.{mod}
open Aeneas Aeneas.Std Result ControlFlow
abbrev E := FIo_Install.NE
def row : Array FIo_Install.NQ 4#usize := FIn_WeightsInstall.mapArray FIo_Install.toQ JGo_TX2_WeightData.f0{tag}
'''
 for i,v in enumerate(vs):s+=f'def v{i} : E := '+x['wide'](v)+'\n'
 s+='def value : E := '+x['wide'](final)+'\n'
 for i in range(4):
  s+=f'''theorem call{i} : FIo_Native.weights.Weights.scalar_factor.closure.Insts.CoreOpsFunctionFnMutPairWideExactUsizeWideExact.call_mut
      (JGq_Powers{tag}.a4,row) (v{i},{i}#usize)=ok (v{i+1},(JGq_Powers{tag}.a4,row)) := by with_unfolding_all rfl
#print axioms call{i}
theorem step{i} : FJg_ScalarFold.body ({{start:={i}#usize,«end»:=4#usize}},(JGq_Powers{tag}.a4,row),v{i})=
    ok (.cont ({{start:={i+1}#usize,«end»:=4#usize}},(JGq_Powers{tag}.a4,row),v{i+1})) := by
  change FIo_Native.core.iter.traits.iterator.Iterator.fold.default_loop.body
    FJg_ScalarFold.iterator FJg_ScalarFold.operation
    {{start:={i}#usize,«end»:=4#usize}} (JGq_Powers{tag}.a4,row) v{i}=_
  unfold FIo_Native.core.iter.traits.iterator.Iterator.fold.default_loop.body
  dsimp only [FJg_ScalarFold.iterator,core.iter.traits.iterator.IteratorRange,FJg_ScalarFold.operation]
  rw [JGo_TX2_Range.next {i}#usize 4#usize {i+1}#usize (by decide) (by decide),bind_tc_ok]
  simp only [Aeneas.Std.uncurry]
  rw [call{i}]
  with_unfolding_all rfl
#print axioms step{i}
'''
 s+=f'''def states : Nat → FJg_ScalarFold.State
'''
 for i in range(4):s+=f'  | {i} => ({{start:={i}#usize,«end»:=4#usize}},(JGq_Powers{tag}.a4,row),v{i})\n'
 s+=f'''  | _ => ({{start:=4#usize,«end»:=4#usize}},(JGq_Powers{tag}.a4,row),v4)
theorem folded : loop FJg_ScalarFold.body (states 0)=ok v4 := by
  apply JGo_TX2_LoopChain.source FJg_ScalarFold.body states 4 v4
  · intro i hi
    interval_cases i
    · exact step0
    · exact step1
    · exact step2
    · exact step3
  · unfold FJg_ScalarFold.body FIo_Native.core.iter.traits.iterator.Iterator.fold.default_loop.body
    with_unfolding_all rfl
#print axioms folded
theorem scaled : FIo_Native.aspis_core.field.wide_exact.WideExact.mul_m31 v4 FIo_Native.weights.QUARTER=ok value := by with_unfolding_all rfl
#print axioms scaled
theorem source : FIo_Native.weights.Weights.scalar_factor row JGq_Powers{tag}.a4=ok value := by
  have run : FIo_Native.core.iter.traits.iterator.Iterator.fold.default FJg_ScalarFold.iterator FJg_ScalarFold.operation
      {{start:=0#usize,«end»:=4#usize}} FIo_Native.aspis_core.field.wide_exact.WideExact.ZERO (JGq_Powers{tag}.a4,row)=ok v4 := by
    unfold FIo_Native.core.iter.traits.iterator.Iterator.fold.default FIo_Native.core.iter.traits.iterator.Iterator.fold.default_loop
    have eta : (fun t : FJg_ScalarFold.State=>match t with
        | (r,c,v)=>FIo_Native.core.iter.traits.iterator.Iterator.fold.default_loop.body
          FJg_ScalarFold.iterator FJg_ScalarFold.operation r c v)=FJg_ScalarFold.body := by
      funext t
      rcases t with ⟨r,c,v⟩
      rfl
    rw [eta]
    with_unfolding_all exact folded
  unfold FIo_Native.weights.Weights.scalar_factor
  rw [run,bind_tc_ok,scaled]
#print axioms source
end AspisR1.{mod}
end
''';out[mod]=s
for mod,t in out.items():
 p=R/'lean'/(mod+'.lean')
 if '--check' in sys.argv:assert p.read_text()==t
 else:p.write_text(t)
print(len(out),'scalar factor stages')
