from pathlib import Path
import sys
R=Path(__file__).resolve().parents[2];x={'__file__':str(R/'evidence/fixture-tx2p-20261027/JGs_preflight.py')};exec((R/'evidence/fixture-tx2p-20261027/JGs_preflight.py').read_text().split('record=')[0],x)
w=x['x']['wide'];parts=x['parts'];libra=x['libra'];mul=x['mul'];add=x['add'];vals=x['vals'];zero=x['zero'];k=x['k'];out={}
def head(imports,ns):return '\n'.join('import '+i for i in imports)+f'\nset_option autoImplicit false\nnoncomputable section\nnamespace AspisR1.{ns}\nopen Aeneas Aeneas.Std Result ControlFlow\nabbrev E := FIo_Install.NE\n'
def end(ns):return f'end AspisR1.{ns}\nend\n'
ns='JGs_PairWrites';s=head(['JGs_K4','JGq_SharedHigh','JGs_Inactive','JGs_LibraSource'],ns)
s+='def initial : Array E 7#usize := (JGq_SharedHigh.write JGs_K4.parts).set 0#usize JGs_Inactive.pair12\n'
p=zero
for j in range(4):
 product=mul(vals[j],libra[j]);v=add(p,product)
 s+=f'def product{j} : E := {w(product)}\ndef v{j+1} : E := {w(v)}\n'
 s+=f'def p{j+1} : Array E 7#usize := initial.set 4#usize v{j+1}\n'
 before='initial' if j==0 else f'p{j}';bv='FIo_Native.aspis_core.field.wide_exact.WideExact.ZERO' if j==0 else f'v{j}'
 s+=f'''theorem mul{j} : FIo_Native.aspis_core.field.wide_exact.WideExact.mul (FIo_Install.toE JGo_TX2_Message00.value{j:02}) (JGs_LibraEnd.value.val[{j}])=ok product{j} := by with_unfolding_all rfl
#print axioms mul{j}
theorem add{j} : FIo_Native.aspis_core.field.wide_exact.WideExact.add {bv} product{j}=ok v{j+1} := by with_unfolding_all rfl
#print axioms add{j}
theorem step{j} : FIo_Native.weights.Weights.pair_loop8.body JGq_PairShape.f JGs_LibraEnd.value
    {{start:={j}#usize,«end»:=4#usize}} {before}=ok (.cont ({{start:={j+1}#usize,«end»:=4#usize}},p{j+1})) := by
  have read : Array.index_usize {before} 4#usize=ok {bv} := by with_unfolding_all rfl
  have lr : Array.index_usize JGs_LibraEnd.value {j}#usize=ok (JGs_LibraEnd.value.val[{j}]) := by rfl
  unfold FIo_Native.weights.Weights.pair_loop8.body
  rw [JGo_TX2_Range.next {j}#usize 4#usize {j+1}#usize (by decide) (by decide),bind_tc_ok]
  simp only [Aeneas.Std.uncurry]
  rw [read,bind_tc_ok,show FIo_Native.weights.field JGq_PairShape.f {j}#usize=ok (FIo_Install.toE JGo_TX2_Message00.value{j:02}) from JGo_TX2_Message00.native_field{j:02},bind_tc_ok,lr,bind_tc_ok,mul{j},bind_tc_ok,add{j},bind_tc_ok]
  with_unfolding_all rfl
#print axioms step{j}
''';p=v
s+='abbrev S := core.ops.range.Range Usize × Array E 7#usize\ndef states : Nat → S\n  | 0 => ({start:=0#usize,«end»:=4#usize},initial)\n'
for j in range(1,4):s+=f'  | {j} => ({{start:={j}#usize,«end»:=4#usize}},p{j})\n'
s+='  | _ => ({start:=4#usize,«end»:=4#usize},p4)\n'
s+='''theorem source : FIo_Native.weights.Weights.pair_loop8 {start:=0#usize,«end»:=4#usize} JGq_PairShape.f initial JGs_LibraEnd.value=ok p4 := by
  unfold FIo_Native.weights.Weights.pair_loop8
  apply JGo_TX2_LoopChain.source
    (fun t : S=>FIo_Native.weights.Weights.pair_loop8.body JGq_PairShape.f JGs_LibraEnd.value t.1 t.2) states 4 p4
  · intro i hi
    interval_cases i
    · exact step0
    · exact step1
    · exact step2
    · exact step3
  · unfold FIo_Native.weights.Weights.pair_loop8.body
    with_unfolding_all rfl
#print axioms source
'''+end(ns);out[ns]=s
ns='JGs_PairSum';s=head(['JGs_PairWrites','JGq_PowersK'],ns);p=zero;power=[1]+[0]*7;s+=f'def v0 : E := {w(p)}\n'
for j in range(7):
 product=mul(power,parts[j]);v=add(p,product)
 s+=f'def product{j} : E := {w(product)}\ndef v{j+1} : E := {w(v)}\n'
 s+=f'''theorem mul{j} : FIo_Native.aspis_core.field.wide_exact.WideExact.mul JGq_PowersK.p{j} (JGs_PairWrites.p4.val[{j}])=ok product{j} := by with_unfolding_all rfl
#print axioms mul{j}
theorem add{j} : FIo_Native.aspis_core.field.wide_exact.WideExact.add v{j} product{j}=ok v{j+1} := by with_unfolding_all rfl
#print axioms add{j}
theorem step{j} : FIo_Native.weights.Weights.pair_loop9.body JGs_PairWrites.p4 JGq_PowersK.a7
    {{start:={j}#usize,«end»:=7#usize}} v{j}=ok (.cont ({{start:={j+1}#usize,«end»:=7#usize}},v{j+1})) := by
  have read : Array.index_usize JGs_PairWrites.p4 {j}#usize=ok (JGs_PairWrites.p4.val[{j}]) := by rfl
  have power : Array.index_usize JGq_PowersK.a7 {j}#usize=ok JGq_PowersK.p{j} := by rfl
  unfold FIo_Native.weights.Weights.pair_loop9.body
  rw [JGo_TX2_Range.next {j}#usize 7#usize {j+1}#usize (by decide) (by decide),bind_tc_ok]
  simp only [Aeneas.Std.uncurry]
  rw [read,bind_tc_ok]
  simp only [FIo_Native.trace.value,bind_tc_ok]
  rw [power,bind_tc_ok,mul{j},bind_tc_ok,add{j},bind_tc_ok]
#print axioms step{j}
''';p=v;power=mul(power,k)
s+='abbrev S := core.ops.range.Range Usize × E\ndef states : Nat → S\n'
for j in range(7):s+=f'  | {j} => ({{start:={j}#usize,«end»:=7#usize}},v{j})\n'
s+='  | _ => ({start:=7#usize,«end»:=7#usize},v7)\n'
s+='''theorem source : FIo_Native.weights.Weights.pair_loop9 {start:=0#usize,«end»:=7#usize} JGs_PairWrites.p4 JGq_PowersK.a7
    FIo_Native.aspis_core.field.wide_exact.WideExact.ZERO=ok v7 := by
  unfold FIo_Native.weights.Weights.pair_loop9
  apply JGo_TX2_LoopChain.source
    (fun t : S=>FIo_Native.weights.Weights.pair_loop9.body JGs_PairWrites.p4 JGq_PowersK.a7 t.1 t.2) states 7 v7
  · intro i hi
    interval_cases i
'''
for j in range(7):s+=f'    · exact step{j}\n'
s+='''  · unfold FIo_Native.weights.Weights.pair_loop9.body
    with_unfolding_all rfl
#print axioms source
'''+end(ns);out[ns]=s
for mod,s in out.items():
 p=R/'lean'/(mod+'.lean')
 if '--check' in sys.argv:assert (p if p.exists() else R/'evidence/fixture-tx2p-20261027/JGs_UNCHECKED'/(p.name+'.txt')).read_text()==s,mod
 else:p.write_text(s)
print(len(out),'bounded final Pair write/sum modules')
