from pathlib import Path
import re
R=Path(__file__).resolve().parents[2]
def limbs(n):
 s=(R/f'lean/JFw_TX2_P{n:02}.lean').read_text().split('def value :')[1].split('theorem')[0]
 return list(map(int,re.findall(r'(\d+)#u32',s)))
coeff=[limbs(n) for n in range(26)]
def wide(nums):
 a=[str(x)+'#u32' for x in nums]
 return f'⟨⟨⟨{a[0]},{a[1]}⟩,⟨{a[2]},{a[3]}⟩⟩,⟨⟨{a[4]},{a[5]}⟩,⟨{a[6]},{a[7]}⟩⟩⟩'
for i in range(10):
 raw=(R/f'lean/JGw_Scalars{i}.lean').read_text()
 arrays=re.findall(r'def values :.*?\[(.*?)\]',raw)
 assert len(arrays)==4
 scalars=[list(map(int,re.findall(r'(\d+)#u32',a))) for a in arrays]
 s=f'''import JHa_DotHeadTransport
import JGw_Dots{i}
import JFw_TX2_CellUnique
set_option autoImplicit false
noncomputable section
namespace AspisR1.JHa_Heads{i}
open Aeneas Aeneas.Std Result
open JFv_TX2_ArrayMeaning (cell)
def data (slot : Fin 4) : JHa_DotContext.Data :=
  ⟨JGw_Dots{i}.q,slot,JGw_Dots{i}.scalar slot,JGw_Dots{i}.reads slot,JGw_Dots{i}.canonical slot⟩
'''
 for slot in range(4):
  vals=[sum(coeff[t][j]*scalars[slot][t] for t in range(26))%2147483647 for j in range(8)]
  s+=f'def value{slot} : FIo_Install.NE := {wide(vals)}\n'
  for j in range(8):
   expr='0'+''.join(f'+{coeff[t][j]}*{scalars[slot][t]}' for t in range(26))
   s+=f'''theorem lane{slot}_{j} : JHa_DotInnerMeaning.sum (data {slot}) {j} 0 26%2147483647={vals[j]} := by
  rw [JHa_DotHeadTransport.source]
  simp only [JHa_DotHeadTransport.sum]
  change ({expr})%2147483647={vals[j]}
  norm_num
#print axioms lane{slot}_{j}
'''
  s+=f'''theorem source{slot} : JFs_TX2_ScalarHead.sourceCall JGw_Dots{i}.q
    JFr_TX2_FirstLane.native {slot}#usize=ok value{slot} := by
  obtain ⟨out,run,_,h⟩ := JHa_DotHeadFlat.source (data {slot})
  have same : out=value{slot} := JFw_TX2_CellUnique.source out value{slot} (by
    intro j
    fin_cases j
'''
  for j in range(8):s+=f'    · exact (h {j}).trans lane{slot}_{j}\n'
  s+=f'''    )
  exact same ▸ run
#print axioms source{slot}
'''
 s+=f'end AspisR1.JHa_Heads{i}\nend\n'
 (R/f'lean/JHa_Heads{i}.lean').write_text(s)
