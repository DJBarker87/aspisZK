from pathlib import Path
import re
R=Path(__file__).resolve().parents[2]
def nums(s):return list(map(int,re.findall(r'(\d+)#u32',s)))
def wide(a):
 a=[str(n)+'#u32' for n in a];return f'⟨⟨⟨{a[0]},{a[1]}⟩,⟨{a[2]},{a[3]}⟩⟩,⟨⟨{a[4]},{a[5]}⟩,⟨{a[6]},{a[7]}⟩⟩⟩'
for i in range(10):
 h=(R/f'lean/JHa_Heads{i}.lean').read_text();t=(R/f'lean/JHa_Tails{i}.lean').read_text()
 s=f'''import JHa_Heads{i}
import JHa_Tails{i}
import JFv_TX2_SlotMeaning
set_option autoImplicit false
noncomputable section
namespace AspisR1.JHa_Dots{i}
open Aeneas Aeneas.Std Result
'''
 for j in range(4):
  a=nums(re.search(rf'def value{j} :.*? := (.*?)\n',h)[1]);b=nums(re.search(rf'def value{j} :.*? := (.*?)\n',t)[1]);v=[(x+y)%2147483647 for x,y in zip(a,b)]
  s+=f'''def value{j} : FIo_Install.NE := {wide(v)}
theorem addition{j} : FIo_Native.aspis_core.field.wide_exact.WideExact.add
    JHa_Heads{i}.value{j} JHa_Tails{i}.value{j}=ok value{j} := by
  with_unfolding_all rfl
#print axioms addition{j}
theorem slot{j} : FIp_NativeDots.fast_dots.four_dots_one JGw_Dots{i}.q
    JFr_TX2_FirstLane.native {j}#usize=ok value{j} := by
  have tail : JFs_TX2_DotSuffix.tail JGw_Dots{i}.q JFr_TX2_FirstLane.native {j}#usize=ok JHa_Tails{i}.value{j} :=
    JHa_Tails{i}.source{j}
  rw [JFv_TX2_SlotMeaning.factor,JHa_Heads{i}.source{j},bind_tc_ok,tail,bind_tc_ok,addition{j}]
#print axioms slot{j}
'''
 s+=f'''def native : Array FIo_Install.NE 4#usize := Array.make 4#usize [value0,value1,value2,value3]
def value : Array FIp_DotsAdapter.E 4#usize := FIp_DotsAdapter.fromArray native

theorem four : FIp_NativeDots.fast_dots.four_dots (JFo_Opening.value ⟨{i},by decide⟩) JFr_TX2_FirstLane.native=ok native := by
  rw [JFs_TX2_FourHead.source]
  change JFs_TX2_FourHead.slots JGw_Dots{i}.q JFr_TX2_FirstLane.native=ok native
  simp only [JFs_TX2_FourHead.slots,slot0,slot1,slot2,slot3,bind_tc_ok]
  rfl
#print axioms four

theorem source : JGw_Dots{i}.value=value := by
  have run := JGw_Dots{i}.source
  change (do let out ← FIp_NativeDots.fast_dots.four_dots (JFo_Opening.value ⟨{i},by decide⟩) JFr_TX2_FirstLane.native
             ok (FIp_DotsAdapter.fromArray out))=ok JGw_Dots{i}.value at run
  rw [four,bind_tc_ok] at run
  exact (Result.ok.inj run).symm
#print axioms source
end AspisR1.JHa_Dots{i}
end
'''
 (R/f'lean/JHa_Dots{i}.lean').write_text(s)
