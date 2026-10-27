from pathlib import Path
import sys
R=Path(__file__).resolve().parents[2]
x={'__file__':str(R/'evidence/fixture-tx2p-20261027/JGs_preflight.py')};exec((R/'evidence/fixture-tx2p-20261027/JGs_preflight.py').read_text().split('libra=')[0],x)
w=x['x']['wide'];add=x['add'];mul=x['mul'];low=x['low'];groups=x['groups'];masks=x['masks'];vals=x['vals'];zero=x['zero']
def head(imports):return '\n'.join('import '+i for i in imports)+'''\nset_option autoImplicit false
noncomputable section
namespace AspisR1.JGs_Inactive
open Aeneas Aeneas.Std Result ControlFlow
'''+('abbrev E := FIo_Install.NE\n' if imports[0]=='JGq_Low' else '')
end='end AspisR1.JGs_Inactive\nend\n';out={};s=head(['JGq_Low','JGq_PairShape','JGq_PartialData'])
cs=[zero[:] for _ in range(12)];s+='def cs0 : Array E 12#usize := Array.make 12#usize ['+','.join(w(v) for v in cs)+']\n'
for j in range(64):
 cs[groups[j]]=add(cs[groups[j]],vals[j]);s+=f'def cs{j+1} : Array E 12#usize := Array.make 12#usize ['+','.join(w(v) for v in cs)+']\n'
weights=[]
for g in range(12):
 v=zero;s+=f'def g{g}w0 : E := {w(v)}\n'
 for b in range(16):
  if masks[g]&(1<<b):v=add(v,low[b])
  s+=f'def g{g}w{b+1} : E := {w(v)}\n'
 weights.append(v)
pair=zero;s+='def pair0 : E := '+w(pair)+'\n'
for g in range(12):pair=add(pair,mul(cs[g],weights[g]));s+=f'def pair{g+1} : E := {w(pair)}\n'
out['JGs_InactiveData']=s+end
for block in range(4):
 s=head(['JGs_InactiveData'])+'attribute [local irreducible] JFw_Frames.window\n'
 for j in range(16*block,16*block+16):
  g=groups[j];owner=f'JGo_TX2_Message{j//8*8:02}'
  s+=f'''theorem coefficient{j} : FIo_Native.weights.s2_grouped_inactive_pair_loop0.body JGq_PairShape.f
    {{start:={j}#usize,«end»:=64#usize}} cs{j}=ok (.cont ({{start:={j+1}#usize,«end»:=64#usize}},cs{j+1})) := by
  have groupRead : Array.index_usize FIo_Native.weights.S2_INACTIVE_GROUPS {j}#usize=ok {g}#u8 := by with_unfolding_all rfl
  have cast : UScalar.cast .Usize {g}#u8={g}#usize := UScalar.eq_of_val_eq (by rw [U8.cast_Usize_val_eq];rfl)
  unfold FIo_Native.weights.s2_grouped_inactive_pair_loop0.body
  rw [JGo_TX2_Range.next {j}#usize 64#usize {j+1}#usize (by decide) (by decide),bind_tc_ok]
  simp only [Aeneas.Std.uncurry,groupRead,lift,bind_tc_ok,cast]
  rw [show FIo_Native.weights.field JGq_PairShape.f {j}#usize=ok (FIo_Install.toE {owner}.value{j:02}) from {owner}.native_field{j:02}]
  with_unfolding_all rfl
#print axioms coefficient{j}
'''
 out[f'JGs_InactiveC{block}']=s+end
s=head([f'JGs_InactiveC{i}' for i in range(4)])+'abbrev CS := core.ops.range.Range Usize × Array E 12#usize\ndef coefficientStates : Nat → CS\n'
for j in range(64):s+=f'  | {j} => ({{start:={j}#usize,«end»:=64#usize}},cs{j})\n'
s+='  | _ => ({start:=64#usize,«end»:=64#usize},cs64)\n'
s+='''theorem coefficients : FIo_Native.weights.s2_grouped_inactive_pair_loop0 {start:=0#usize,«end»:=64#usize} JGq_PairShape.f
    (Array.repeat 12#usize FIo_Native.aspis_core.field.wide_exact.WideExact.ZERO)=ok cs64 := by
  have initial : Array.repeat 12#usize FIo_Native.aspis_core.field.wide_exact.WideExact.ZERO=cs0 := by with_unfolding_all rfl
  rw [initial]
  unfold FIo_Native.weights.s2_grouped_inactive_pair_loop0
  apply JGo_TX2_LoopChain.source
    (fun t : CS=>FIo_Native.weights.s2_grouped_inactive_pair_loop0.body JGq_PairShape.f t.1 t.2) coefficientStates 64 cs64
  · intro i hi
    interval_cases i
'''
for j in range(64):s+=f'    · exact coefficient{j}\n'
s+='''  · unfold FIo_Native.weights.s2_grouped_inactive_pair_loop0.body
    with_unfolding_all rfl
#print axioms coefficients
''';out['JGs_InactiveCoefficients']=s+end
for block in range(4):
 s=head(['JGs_InactiveData'])
 for g in range(3*block,3*block+3):
  for b in range(16):
   s+=f'''theorem weight{g}step{b} : FIo_Native.weights.s2_grouped_inactive_pair_loop1_loop0.body JGq_Low.a16 {g}#usize
    {{start:={b}#usize,«end»:=16#usize}} g{g}w{b}=ok (.cont ({{start:={b+1}#usize,«end»:=16#usize}},g{g}w{b+1})) := by
  unfold FIo_Native.weights.s2_grouped_inactive_pair_loop1_loop0.body
  rw [JGo_TX2_Range.next {b}#usize 16#usize {b+1}#usize (by decide) (by decide),bind_tc_ok]
  simp only [Aeneas.Std.uncurry]
  with_unfolding_all rfl
#print axioms weight{g}step{b}
'''
  s+=f'def weightStates{g} : Nat → core.ops.range.Range Usize × E\n'
  for b in range(16):s+=f'  | {b} => ({{start:={b}#usize,«end»:=16#usize}},g{g}w{b})\n'
  s+=f'  | _ => ({{start:=16#usize,«end»:=16#usize}},g{g}w16)\n'
  s+=f'''theorem weight{g} : FIo_Native.weights.s2_grouped_inactive_pair_loop1_loop0 {{start:=0#usize,«end»:=16#usize}}
    JGq_Low.a16 {g}#usize FIo_Native.aspis_core.field.wide_exact.WideExact.ZERO=ok g{g}w16 := by
  have initial : FIo_Native.aspis_core.field.wide_exact.WideExact.ZERO=g{g}w0 := by with_unfolding_all rfl
  rw [initial]
  unfold FIo_Native.weights.s2_grouped_inactive_pair_loop1_loop0
  apply JGo_TX2_LoopChain.source
    (fun t : core.ops.range.Range Usize × E=>FIo_Native.weights.s2_grouped_inactive_pair_loop1_loop0.body JGq_Low.a16 {g}#usize t.1 t.2)
    weightStates{g} 16 g{g}w16
  · intro i hi
    interval_cases i
'''
  for b in range(16):s+=f'    · exact weight{g}step{b}\n'
  s+='  · unfold FIo_Native.weights.s2_grouped_inactive_pair_loop1_loop0.body\n    with_unfolding_all rfl\n'+f'#print axioms weight{g}\n'
 out[f'JGs_InactiveW{block}']=s+end
s=head(['JGs_InactiveCoefficients']+[f'JGs_InactiveW{i}' for i in range(4)])
for g in range(12):
 s+=f'''theorem group{g} : FIo_Native.weights.s2_grouped_inactive_pair_loop1.body JGq_Low.a16 cs64
    {{start:={g}#usize,«end»:=12#usize}} pair{g}=ok (.cont ({{start:={g+1}#usize,«end»:=12#usize}},pair{g+1})) := by
  unfold FIo_Native.weights.s2_grouped_inactive_pair_loop1.body
  rw [JGo_TX2_Range.next {g}#usize 12#usize {g+1}#usize (by decide) (by decide),bind_tc_ok]
  simp only [Aeneas.Std.uncurry]
  rw [weight{g},bind_tc_ok]
  with_unfolding_all rfl
#print axioms group{g}
'''
s+='def pairStates : Nat → core.ops.range.Range Usize × E\n'
for g in range(12):s+=f'  | {g} => ({{start:={g}#usize,«end»:=12#usize}},pair{g})\n'
s+='  | _ => ({start:=12#usize,«end»:=12#usize},pair12)\n'
s+='''theorem paired : FIo_Native.weights.s2_grouped_inactive_pair_loop1 {start:=0#usize,«end»:=12#usize} JGq_Low.a16 cs64
    FIo_Native.aspis_core.field.wide_exact.WideExact.ZERO=ok pair12 := by
  have initial : FIo_Native.aspis_core.field.wide_exact.WideExact.ZERO=pair0 := by with_unfolding_all rfl
  rw [initial]
  unfold FIo_Native.weights.s2_grouped_inactive_pair_loop1
  apply JGo_TX2_LoopChain.source
    (fun t : core.ops.range.Range Usize × E=>FIo_Native.weights.s2_grouped_inactive_pair_loop1.body JGq_Low.a16 cs64 t.1 t.2) pairStates 12 pair12
  · intro i hi
    interval_cases i
'''
for g in range(12):s+=f'    · exact group{g}\n'
s+='''  · unfold FIo_Native.weights.s2_grouped_inactive_pair_loop1.body
    with_unfolding_all rfl
#print axioms paired
theorem source : FIo_Native.weights.grouped_inactive_pair JGq_PairShape.w JGq_PairShape.f JGq_Low.a16=ok pair12 := by
  have variant : FIo_Native.transport.Variant.Insts.CoreCmpPartialEqVariant.eq JGq_PairShape.w.variant .S2=ok true := by
    change FIo_Native.transport.Variant.Insts.CoreCmpPartialEqVariant.eq .S2 .S2=ok true
    unfold FIo_Native.transport.Variant.Insts.CoreCmpPartialEqVariant.eq FIo_Native.transport.Variant.read_discriminant
    simp only [eq_self,decide_true]
  have width : Usize.wrapping_mul 64#usize 32#usize=2048#usize :=
    UScalar.eq_of_val_eq (Port3_Wrapping.wrap_mul_value 64#usize 32#usize (by decide))
  unfold FIo_Native.weights.grouped_inactive_pair
  rw [variant,bind_tc_ok]
  simp only [ite_true,eq_self,JGq_PairShape.length,lift,bind_tc_ok,width]
  unfold FIo_Native.weights.s2_grouped_inactive_pair
  simp only [coefficients,bind_tc_ok,paired]
#print axioms source
''';out['JGs_Inactive']=s+end
for mod,s in out.items():
 p=R/'lean'/(mod+'.lean')
 if '--check' in sys.argv:assert p.read_text()==s,mod
 else:p.write_text(s)
print(len(out),'bounded inactive modules')
