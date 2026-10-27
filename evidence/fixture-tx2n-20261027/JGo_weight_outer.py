from pathlib import Path
P=Path(__file__).resolve().parent;R=P.parents[1]
s='''import JGo_TX2_WeightRows
import JGo_TX2_WeightPoints
import JGo_TX2_Range
set_option autoImplicit false
noncomputable section
namespace AspisR1.JGo_TX2_WeightConstruct
open Aeneas Aeneas.Std Result ControlFlow FIn_WeightsExtract JGo_TX2_WeightData
abbrev Range := core.ops.range.Range Usize
'''
for k in range(3):
 s+=f'''theorem first{k} : weights_new_loop0.body points {{start:={k}#usize,«end»:=3#usize}} factors{5*k:02}=
    ok (.cont ({{start:={k+1}#usize,«end»:=3#usize}},factors{5*(k+1):02})) := by
  unfold weights_new_loop0.body
  rw [JGo_TX2_Range.next {k}#usize 3#usize {k+1}#usize (by decide) (by decide)]
  simp only [bind_tc_ok]
  rw [JGo_TX2_WeightRows.inner{k},bind_tc_ok]
#print axioms first{k}
'''
s+='''def firstStates : Nat → Range × Factors
  | 0 => ({start:=0#usize,«end»:=3#usize},factors00)
  | 1 => ({start:=1#usize,«end»:=3#usize},factors05)
  | 2 => ({start:=2#usize,«end»:=3#usize},factors10)
  | _ => ({start:=3#usize,«end»:=3#usize},factors15)
theorem firstLoop : weights_new_loop0 {start:=0#usize,«end»:=3#usize} points factors00=ok factors15 := by
  unfold weights_new_loop0
  apply JGo_TX2_LoopChain.source (fun s : Range × Factors=>match s with | (iter,factors)=>weights_new_loop0.body points iter factors)
    firstStates 3 factors15
  · intro i hi
    interval_cases i
    · exact first0
    · exact first1
    · exact first2
  · rfl
#print axioms firstLoop
'''
for p in range(2):
 k=p+3;n=k*5
 rows=[f'r{j}_5' if j<k else ('(Array.make 5#usize [Array.make 4#usize [field.QM31.ONE,z'+str(p)+'y,z'+str(p)+'x,q],'+','.join(['Array.repeat 4#usize field.QM31.ZERO']*4)+'])') if j==k else f'r{j}_0' for j in range(5)]
 s+=f'def seeded{p} (q : Q) : Factors := Array.make 5#usize ['+','.join(rows)+']\n'
 s+=f'''theorem second{p} : weights_new_loop1.body z {{start:={p}#usize,«end»:=2#usize}} factors{n:02}=
    ok (.cont ({{start:={p+1}#usize,«end»:=2#usize}},factors{n+5:02})) := by
  have index : Usize.wrapping_add 3#usize {p}#usize={k}#usize :=
    UScalar.eq_of_val_eq (Port3_Wrapping.wrap_add_value 3#usize {p}#usize (by decide))
  unfold weights_new_loop1.body
  rw [JGo_TX2_Range.next {p}#usize 2#usize {p+1}#usize (by decide) (by decide)]
  simp only [lift,bind_tc_ok,index]
  change (do
    let q ← field.QM31.mul z{p}x z{p}y
    let x ← double z{p}x
    let out ← weights_new_loop1_loop0 {{start:=1#usize,«end»:=5#usize}} (seeded{p} q) {p}#usize x
    ok (.cont ({{start:={p+1}#usize,«end»:=2#usize}},out)))=_
  rw [JGo_TX2_WeightRow{k}.product,bind_tc_ok,JGo_TX2_WeightRow{k}.double,bind_tc_ok]
  change (do
    let out ← weights_new_loop1_loop0 {{start:=1#usize,«end»:=5#usize}} factors{n+1:02} {p}#usize x{p}_1
    ok (.cont ({{start:={p+1}#usize,«end»:=2#usize}},out)))=_
  rw [JGo_TX2_WeightRows.inner{k},bind_tc_ok]
#print axioms second{p}
'''
s+='''def secondStates : Nat → Range × Factors
  | 0 => ({start:=0#usize,«end»:=2#usize},factors15)
  | 1 => ({start:=1#usize,«end»:=2#usize},factors20)
  | _ => ({start:=2#usize,«end»:=2#usize},factors25)
theorem secondLoop : weights_new_loop1 {start:=0#usize,«end»:=2#usize} z factors15=ok factors25 := by
  unfold weights_new_loop1
  apply JGo_TX2_LoopChain.source (fun s : Range × Factors=>match s with | (iter,factors)=>weights_new_loop1.body z iter factors)
    secondStates 2 factors25
  · intro i hi
    interval_cases i
    · exact second0
    · exact second1
  · rfl
#print axioms secondLoop
end AspisR1.JGo_TX2_WeightConstruct
end
'''
(R/'lean/JGo_TX2_WeightConstruct.lean').write_text(s)
