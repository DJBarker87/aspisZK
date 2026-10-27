from pathlib import Path
import sys
R=Path(__file__).resolve().parents[2];out={};perm=[0,3,2,1]
for side in [0,1]:
 ns=f'JGs_LibraStage{side}'
 s=f'''import FJm_LibraStages
import JGs_LibraPowers{side}
import JGs_LibraTerms{side}
import JGs_LibraWrites
set_option autoImplicit false
noncomputable section
namespace AspisR1.{ns}
open Aeneas Aeneas.Std Result ControlFlow
open JGs_Libra JGs_LibraEnd
abbrev E := FIo_Install.NE
abbrev Q := FIo_Install.NQ
def high : Array Q 4#usize := Array.make 4#usize [q{side}_0,q{side}_4,q{side}_8,q{side}_12]
theorem powers : FJm_LibraStages.powers (FIo_Install.toWeights JGo_TX2_WeightData.value).extra {side}#usize=
    ok (row{side},high,q{side}_4,q{side}_16) := by
  unfold FJm_LibraStages.powers
  rw [extra{side},bind_tc_ok,power{side}_0,bind_tc_ok,power{side}_1,bind_tc_ok,power{side}_2,bind_tc_ok,power{side}_3,bind_tc_ok]
  have read : Array.index_usize (Array.make 4#usize [FIo_Native.aspis_core.field.QM31.ONE,q{side}_1,q{side}_2,q{side}_3]) 2#usize=ok q{side}_2 := by rfl
  rw [read,bind_tc_ok,power{side}_4,bind_tc_ok,power{side}_5,bind_tc_ok,power{side}_6,bind_tc_ok,power{side}_7,bind_tc_ok]
  rw [JGs_LibraWrites.one{side}]
  rfl
#print axioms powers
'''
 for j in range(4):
  s+=f'''theorem term{j} : FJm_LibraStages.term JGq_Powers1.a4 high {j}#usize=ok ({perm[j]}#usize,JGs_Libra.term{side}_{j}) := by
  have perm : Array.index_usize FIo_Native.weights.PERM {j}#usize=ok {perm[j]}#usize := by with_unfolding_all rfl
  have ap : Array.index_usize JGq_Powers1.a4 {perm[j]}#usize=ok JGq_Powers1.p{perm[j]} := by rfl
  have read : Array.index_usize high {j}#usize=ok q{side}_{4*j} := by rfl
  unfold FJm_LibraStages.term
  rw [perm,bind_tc_ok,ap,bind_tc_ok,read,bind_tc_ok,mixed{side}_{j},bind_tc_ok,quarter{side}_{j},bind_tc_ok]
#print axioms term{j}
'''
 s+=f'''theorem totals : FJm_LibraStages.totals (Array.make 4#usize [JGs_Libra.term{side}_0,JGs_Libra.term{side}_1,JGs_Libra.term{side}_2,JGs_Libra.term{side}_3])=
    ok (sum{side}_2,sum{side}_3,sum{side}_4) := by
'''
 for j in range(4):s+=f'  have read{j} : Array.index_usize (Array.make 4#usize [JGs_Libra.term{side}_0,JGs_Libra.term{side}_1,JGs_Libra.term{side}_2,JGs_Libra.term{side}_3]) {j}#usize=ok JGs_Libra.term{side}_{j} := by rfl\n'
 s+=f'''  unfold FJm_LibraStages.totals
  rw [read0,bind_tc_ok,read1,bind_tc_ok,sum{side}call2,bind_tc_ok,read2,bind_tc_ok,sum{side}call3,bind_tc_ok,read3,bind_tc_ok,sum{side}call4,bind_tc_ok]
#print axioms totals
'''
 before='initial' if side==0 else 'middle';after='middle' if side==0 else 'value'
 s+=f'''theorem finish : FJm_LibraStages.finish {side}#usize JGs_LibraScale{side}.value 1#usize sum{side}_2 sum{side}_3 sum{side}_4
    q{side}_4 q{side}_16 JGq_Powers1.a4 JGs_LibraEnd.{before} {{start:={side+1}#usize,«end»:=2#usize}}=
    ok (.cont ({{start:={side+1}#usize,«end»:=2#usize}},JGs_LibraEnd.{after})) := by
  unfold FJm_LibraStages.finish
'''
 if side==0:s+='''  simp only [ite_true]
  rw [call_a,bind_tc_ok,JGs_LibraWrites.up0,bind_tc_ok,call_b,bind_tc_ok,call_c,bind_tc_ok,JGs_LibraWrites.up1,bind_tc_ok]
'''
 else:s+='''  simp only [show ¬(1#usize=0#usize) from by decide,ite_false]
  have ap : Array.index_usize JGq_Powers1.a4 1#usize=ok JGq_Powers1.p1 := by rfl
  rw [JGs_LibraWrites.read,bind_tc_ok,ap,bind_tc_ok,call_d,bind_tc_ok,call_e,bind_tc_ok,call_f,bind_tc_ok,
    JGs_LibraWrites.up2,bind_tc_ok,call_g,bind_tc_ok,call_h,bind_tc_ok,JGs_LibraWrites.up3,bind_tc_ok,
    call_i,bind_tc_ok,power1_8,bind_tc_ok,call_j,bind_tc_ok,JGs_LibraWrites.up4,bind_tc_ok]
'''
 s+=f'#print axioms finish\nend AspisR1.{ns}\nend\n';out[ns]=s
s='''import JGs_LibraStage0
import JGs_LibraStage1
set_option autoImplicit false
noncomputable section
namespace AspisR1.JGs_LibraNative
open Aeneas Aeneas.Std Result ControlFlow
'''
for side in [0,1]:
 before='initial' if side==0 else 'middle';after='middle' if side==0 else 'value';ns=f'JGs_LibraStage{side}'
 s+=f'''theorem step{side} : FIo_Native.weights.factored_s2_libra_weights_loop.body JGq_Powers0.a4 JGq_Powers1.a4
    (FIo_Install.toWeights JGo_TX2_WeightData.value).extra {{start:={side}#usize,«end»:=2#usize}} JGs_LibraEnd.{before}=
    ok (.cont ({{start:={side+1}#usize,«end»:=2#usize}},JGs_LibraEnd.{after})) := by
  rw [JGs_LibraProgram.source]
  unfold JGs_LibraProgram.body
  rw [JGo_TX2_Range.next {side}#usize 2#usize {side+1}#usize (by decide) (by decide),bind_tc_ok]
  simp only [Aeneas.Std.uncurry,{ns}.powers,bind_tc_ok,JGs_LibraScale{side}.source,
    {ns}.term0,{ns}.term1,{ns}.term2,{ns}.term3,{ns}.totals,{ns}.finish]
#print axioms step{side}
'''
s+='end AspisR1.JGs_LibraNative\nend\n';out['JGs_LibraNativeSplit']=s
# The old memory-rejected Native0/1 stay separate and are not imported here.
source=(R/'lean/JGs_LibraSource.lean').read_text().replace('import JGs_LibraNative0\nimport JGs_LibraNative1','import JGs_LibraNativeSplit');out['JGs_LibraSource']=source
for mod,s in out.items():
 p=R/'lean'/(mod+'.lean')
 if '--check' in sys.argv:assert p.read_text()==s,mod
 else:p.write_text(s)
print(len(out),'Libra stage factorization modules')
