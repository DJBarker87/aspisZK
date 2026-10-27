from pathlib import Path
import json,sys
def emit(path,text):
 p=Path(path)
 if "--check" in sys.argv:assert p.read_text()==text,str(p)
 else:p.write_text(text)
P=2147483647
raw=json.loads(Path('evidence/fixture-tx2g-20261026/JFw_RAW.json').read_text())
def rec(xs):
 if len(xs)==1:return str(xs[0])+'#u32'
 n=len(xs)//2;return '⟨'+rec(xs[:n])+','+rec(xs[n:])+'⟩'
for slot in range(4):
 sums=raw[slot*3+2]['after'];nums=[x%P for x in sums]
 mod=f'JFw_TX2_Tail{slot}'
 s=f'''import JFw_TX2_Raw{slot}2
import JFw_TX2_PowerReads
import JFw_TX2_CellUnique
import JFv_TX2_EbyKFinishMeaning
set_option autoImplicit false
noncomputable section
namespace AspisR1.{mod}
open Aeneas Aeneas.Std Result
open JFs_TX2_RawMap
def value : FIo_Install.NE := {rec(nums)}
theorem finish : FIo_Native.fast_pairing.EbyKDot.finish JFw_TX2_Raw{slot}2.after=ok value := by
  obtain ⟨out,a,b,run,_,h,va,vb⟩ := JFv_TX2_EbyKFinishMeaning.source JFw_TX2_Raw{slot}2.after
  obtain ⟨a0,a1,a2,a3,ea⟩ := shape a
  obtain ⟨a4,a5,a6,a7,eb⟩ := shape b
  rw [ea] at va
  rw [eb] at vb
'''
 for j in range(8):
  s+=f'''  have h{j} := {'va' if j<4 else 'vb'} {j%4}
  change a{j}.val={sums[j]}%2147483647 at h{j}
  norm_num at h{j}
  have e{j} : a{j}={nums[j]}#u32 := UScalar.eq_of_val_eq h{j}
'''
 s+='  rw [ea,eb,'+','.join(f'e{j}' for j in range(8))+'] at h\n'
 s+='''  have limbs : JFv_TX2_FromLimbsMeaning.limbs out=JFv_TX2_FromLimbsMeaning.limbs value := Subtype.ext h
  have same : out=value := JFw_TX2_CellUnique.source out value (by intro j;rw [limbs])
  exact same ▸ run
'''
 s+=f'''theorem source : JFs_TX2_DotSuffix.tail
    (JFr_TX2_Windows.array (JFn_Values.position 0)) JFr_TX2_FirstLane.native {slot}#usize=ok value := by
  have g28 := JFw_TX2_PowerReads.source 28
  have g26 := JFw_TX2_PowerReads.source 26
  have g27 := JFw_TX2_PowerReads.source 27
  change Array.index_usize JFr_TX2_FirstLane.native 28#usize=ok JFw_TX2_P28.value at g28
  change Array.index_usize JFr_TX2_FirstLane.native 26#usize=ok JFw_TX2_P26.value at g26
  change Array.index_usize JFr_TX2_FirstLane.native 27#usize=ok JFw_TX2_P27.value at g27
  erw [JFs_TX2_TailStages.body _ _ ({slot}:Fin 4)]
  simp only [JFs_TX2_TailStages.source,bind_tc_ok,g28,g26,g27,
    show FIo_Native.fast_pairing.EbyKDot.new=ok JFw_TX2_Raw{slot}0.before from rfl,
    show JFr_TX2_TailRead.read (JFr_TX2_Windows.array (JFn_Values.position 0))
      (JFr_TX2_Tails.offset {slot} 0) (JFr_TX2_Tails.stop {slot} 0)=ok JFr_TX2_Tails10.value0_{slot}
      from JFr_TX2_Tails10.source0_{slot},
    show JFr_TX2_TailRead.read (JFr_TX2_Windows.array (JFn_Values.position 0))
      (JFr_TX2_Tails.offset {slot} 1) (JFr_TX2_Tails.stop {slot} 1)=ok JFr_TX2_Tails10.value1_{slot}
      from JFr_TX2_Tails10.source1_{slot},
    show JFr_TX2_TailRead.read (JFr_TX2_Windows.array (JFn_Values.position 0))
      (JFr_TX2_Tails.offset {slot} 2) (JFr_TX2_Tails.stop {slot} 2)=ok JFr_TX2_Tails10.value2_{slot}
      from JFr_TX2_Tails10.source2_{slot},
    JFw_TX2_Raw{slot}0.source,Aeneas.Std.uncurry,core.result.Result.unwrap]
  have same1 : JFw_TX2_Raw{slot}0.after=JFw_TX2_Raw{slot}1.before := rfl
  have same2 : JFw_TX2_Raw{slot}1.after=JFw_TX2_Raw{slot}2.before := rfl
  simp only [same1,JFw_TX2_Raw{slot}1.source,bind_tc_ok,Aeneas.Std.uncurry,
    core.result.Result.unwrap,same2,JFw_TX2_Raw{slot}2.source,finish]
#print axioms finish
#print axioms source
end AspisR1.{mod}
end
'''
 emit('lean/'+mod+'.lean',s)
