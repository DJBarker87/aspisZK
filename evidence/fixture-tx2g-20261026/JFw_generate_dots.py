from pathlib import Path
import json,sys
def emit(path,text):
 p=Path(path)
 if "--check" in sys.argv:assert p.read_text()==text,str(p)
 else:p.write_text(text)
v=json.loads(Path('evidence/fixture-tx2g-20261026/JFw_NUMERIC_PREFLIGHT.json').read_text())
def rec(xs,suf=''):
 if len(xs)==1:return str(xs[0])+suf
 n=len(xs)//2;return '⟨'+rec(xs[:n],suf)+','+rec(xs[n:],suf)+'⟩'
def canon(nums):
 return f'''  change (({nums[0]}<2147483647 ∧ {nums[1]}<2147483647) ∧ ({nums[2]}<2147483647 ∧ {nums[3]}<2147483647)) ∧
    (({nums[4]}<2147483647 ∧ {nums[5]}<2147483647) ∧ ({nums[6]}<2147483647 ∧ {nums[7]}<2147483647))
  omega
'''
h=json.loads(Path('evidence/fixture-tx2g-20261026/JFw_HEADS.json').read_text())
for slot,nums in enumerate(v['dots']):
 mod=f'JFw_TX2_Dot{slot}'
 s=f'''import JFw_TX2_Head{slot}
import JFw_TX2_Tail{slot}
import JFv_TX2_SlotMeaning
set_option autoImplicit false
noncomputable section
namespace AspisR1.{mod}
open Aeneas Aeneas.Std Result
open JFw_TX2_PowersExplicit (decode)
def value : FIo_Install.NE := {rec(nums,'#u32')}
theorem canonical : FIo_WideValues.Canon value := by
'''+canon(nums)
 s+=f'''theorem addition : decode JFw_TX2_Head{slot}.value+decode JFw_TX2_Tail{slot}.value=decode value := by
  change ({rec(h[slot])} : AspisWideTower.WideExact)+{rec(v['tails'][slot])}={rec(nums)}
  ext <;> norm_num [AspisV8R15.ExactTowerBase.M31Exact,AspisV8R15.ExactTowerBase.P] <;> decide

theorem source : FIp_NativeDots.fast_dots.four_dots_one
    (JFr_TX2_Windows.array (JFn_Values.position 0)) JFr_TX2_FirstLane.native {slot}#usize=ok value := by
  obtain ⟨out,run,co⟩ := JFs_TX2_Slot.source 0 {slot}
  have us : Usize.ofNat ({slot}:Fin 4).val (by have:=({slot}:Fin 4).isLt;scalar_tac)={slot}#usize := by
    apply UScalar.eq_of_val_eq;rfl
  rw [us] at run
  have add : FIo_Native.aspis_core.field.wide_exact.WideExact.add
      JFw_TX2_Head{slot}.value JFw_TX2_Tail{slot}.value=ok out := by
    simpa only [JFv_TX2_SlotMeaning.factor,JFw_TX2_Head{slot}.source,
      JFw_TX2_Tail{slot}.source,bind_tc_ok] using run
  have ch : FIo_WideValues.Canon JFw_TX2_Head{slot}.value := by
'''+''.join('  '+x+'\n' for x in canon(h[slot]).rstrip().splitlines())
 s+=f'''  have ct : FIo_WideValues.Canon JFw_TX2_Tail{slot}.value := by
'''+''.join('  '+x+'\n' for x in canon(v['tails'][slot]).rstrip().splitlines())
 s+=f'''  have sem := (FIo_WideValues.add _ _ _ ch ct add).2
  have same : out=value := JFw_TX2_ValueUnique.native out value co canonical (sem.trans addition)
  exact same ▸ run
#print axioms canonical
#print axioms addition
#print axioms source
end AspisR1.{mod}
end
'''
 emit('lean/'+mod+'.lean',s)
s=''.join(f'import JFw_TX2_Dot{k}\n' for k in range(4))+'''set_option autoImplicit false
noncomputable section
namespace AspisR1.JFw_TX2_Dots0
open Aeneas Aeneas.Std Result
def native : Array FIo_Install.NE 4#usize := Array.make 4#usize
  [JFw_TX2_Dot0.value,JFw_TX2_Dot1.value,JFw_TX2_Dot2.value,JFw_TX2_Dot3.value]
def value := FIp_DotsAdapter.fromArray native

theorem source : JFs_TX2_Dots.value 0=value := by
  apply JFw_TX2_DotsExplicit.chosen
  rw [JFs_TX2_FourHead.source]
  simp only [JFs_TX2_FourHead.slots,JFw_TX2_Dot0.source,JFw_TX2_Dot1.source,
    JFw_TX2_Dot2.source,JFw_TX2_Dot3.source,bind_tc_ok]
  rfl
#print axioms source
end AspisR1.JFw_TX2_Dots0
end
'''
emit('lean/JFw_TX2_Dots0.lean',s)
