from pathlib import Path
import sys
R=Path(__file__).resolve().parents[2]
x={'__file__':str(R/'evidence/fixture-tx2o-20261027/JGq_partial.py')};exec((R/'evidence/fixture-tx2o-20261027/JGq_partial.py').read_text().split('out={};t=')[0],x)
y={'__file__':str(R/'evidence/fixture-tx2p-20261027/JGs_tensor.py')};exec((R/'evidence/fixture-tx2p-20261027/JGs_tensor.py').read_text().split('for mod,s in out.items():')[0],y)
q=y['q'];header=y['header'];end=y['end'];out={}
for k in [1,3,4]:
 ns=f'JGs_D{k}';cs=x['nums'] if 'nums' in x else x['x']['nums']
 data=y['out'][f'JGs_T{k}Data'];import re
 line=re.search(r'def s21[^\n]*',data).group(0);nums=list(map(int,re.findall(r'(\d+)#u32',line)));coeff=[nums[i:i+4] for i in range(0,256,4)]
 t=header([f'JGs_T{k}Data','JGq_PartialData'],ns)
 for j,v in enumerate(coeff):t+=f'def q{j} : FIo_Install.NQ := {q(v)}\n'
 sums=[0]*8;t+=f'def d0 : FIo_Native.fast_pairing.EbyKDot := {x["state"](sums,0)}\n'
 for j in range(64):
  v=x['values'][j];raws=x['raw'](v[:4],coeff[j])+x['raw'](v[4:],coeff[j]);sums=[(old+x['fold'](r))&x['MASK'] for old,r in zip(sums,raws)]
  t+=f'def d{j+1} : FIo_Native.fast_pairing.EbyKDot := {x["state"](sums,j+1)}\n'
 t+='def value : FIo_Install.NE := '+x['x']['wide']([v%x['P'] for v in sums])+'\n'
 t+=end(ns);out[ns+'Data']=t
 for block in range(4):
  t=header([ns+'Data'],ns)+'attribute [local irreducible] JFw_Frames.window\n'
  for j in range(block*16,block*16+16):
   owner=f'JGo_TX2_Message{(j//8)*8:02}';v=f'FIo_Install.toE {owner}.value{j:02}'
   t+=f'''theorem push{j} : FIo_Native.fast_pairing.EbyKDot.push d{j} ({v}) q{j}=ok (.Ok (),d{j+1}) := by
  have inc : Usize.wrapping_add d{j}.count 1#usize={j+1}#usize :=
    UScalar.eq_of_val_eq (Port3_Wrapping.wrap_add_value d{j}.count 1#usize (by decide))
  simp only [FIo_Native.fast_pairing.EbyKDot.push,
    FIo_Native.fast_pairing.canonical.Dot.push,JGq_DotLoop.source,inc]
  with_unfolding_all rfl
#print axioms push{j}
'''
  t+=end(ns);out[ns+f'Push{block}']=t
 t=header([ns+f'Push{i}' for i in range(4)],ns)+'attribute [local irreducible] JFw_Frames.window\n'
 for j in range(64):
  owner=f'JGo_TX2_Message{(j//8)*8:02}'
  t+=f'''theorem step{j} : FIo_Native.weights.push_byte_products_loop.body JGq_PairShape.f JGs_T{k}.s21
    {{start:={j}#usize,«end»:=64#usize}} d{j}=ok (.cont ({{start:={j+1}#usize,«end»:=64#usize}},d{j+1})) := by
  have read : Slice.index_usize JGs_T{k}.s21 {j}#usize=ok q{j} := by rfl
  unfold FIo_Native.weights.push_byte_products_loop.body
  rw [JGo_TX2_Range.next {j}#usize 64#usize {j+1}#usize (by decide) (by decide),bind_tc_ok]
  simp only [Aeneas.Std.uncurry]
  rw [show FIo_Native.weights.field JGq_PairShape.f {j}#usize=ok (FIo_Install.toE {owner}.value{j:02}) from {owner}.native_field{j:02},bind_tc_ok,
    read,bind_tc_ok,push{j},bind_tc_ok]
  rfl
#print axioms step{j}
'''
 t+='abbrev S := core.ops.range.Range Usize × FIo_Native.fast_pairing.EbyKDot\ndef states : Nat → S\n'
 for j in range(64):t+=f'  | {j} => ({{start:={j}#usize,«end»:=64#usize}},d{j})\n'
 t+='  | _ => ({start:=64#usize,«end»:=64#usize},d64)\n'
 t+=f'''theorem source : FIo_Native.weights.push_byte_products d0 JGq_PairShape.f JGs_T{k}.s21 64#usize=ok (.Ok (),d64) := by
  unfold FIo_Native.weights.push_byte_products FIo_Native.weights.push_byte_products_loop
  apply JGo_TX2_LoopChain.source
    (fun t : S=>FIo_Native.weights.push_byte_products_loop.body JGq_PairShape.f JGs_T{k}.s21 t.1 t.2) states 64 (.Ok (),d64)
  · intro i hi
    interval_cases i
'''
 for j in range(64):t+=f'    · exact step{j}\n'
 t+='''  · unfold FIo_Native.weights.push_byte_products_loop.body
    with_unfolding_all rfl
#print axioms source
theorem finish : FIo_Native.fast_pairing.EbyKDot.finish d64=ok value := by with_unfolding_all rfl
#print axioms finish
'''+end(ns);out[ns]=t
for mod,s in out.items():
 p=R/'lean'/(mod+'.lean')
 if '--check' in sys.argv:assert p.read_text()==s,mod
 else:p.write_text(s)
print(len(out),'bounded regular-dot modules')
