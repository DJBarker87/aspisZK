"""Numeric head instances: symbolic source transport precedes finite arithmetic."""
from pathlib import Path
import re,json,sys
P=2147483647
v=json.loads(Path('evidence/fixture-tx2g-20261026/JFw_POWERS.json').read_text())
def emit(path,text):
 p=Path(path)
 if '--check' in sys.argv:assert p.read_text()==text,str(p)
 else:p.write_text(text)
def rec(a):
 if len(a)==1:return str(a[0])+'#u32'
 n=len(a)//2;return '⟨'+rec(a[:n])+','+rec(a[n:])+'⟩'
heads=[]
for slot in range(4):
 text=Path(f'lean/JFr_TX2_Slot10_{slot}.lean').read_text()
 scalars=list(map(int,re.findall(r'(\d+)#u32',re.search(r'def values[^\n]+',text)[0])))
 nums=[sum(v[t][j]*scalars[t] for t in range(26))%P for j in range(8)];heads.append(nums)
 groups=[[0],[1,2,3],[4,5,6,7]] if slot==0 else [[0,1,2,3],[4,5,6,7]]
 names=['Head00','Head0Lo','Head0Hi'] if slot==0 else [f'Head{slot}Lo',f'Head{slot}Hi']
 for js,name in zip(groups,names):
  s=f'''import JFw_TX2_HeadTransport
set_option autoImplicit false
noncomputable section
namespace AspisR1.JFw_TX2_{name}
open Aeneas Aeneas.Std Result
'''
  for j in js:
   expr='0'+''.join(f'+{v[t][j]}*{scalars[t]}' for t in range(26))
   s+=f'''theorem lane{j} : JFv_TX2_InnerMeaning.sum 0 {slot} {j} 0 26%2147483647={nums[j]} := by
  rw [JFw_TX2_HeadTransport.source]
  simp only [JFw_TX2_HeadTransport.sum]
  change ({expr})%2147483647={nums[j]}
  norm_num
#print axioms lane{j}
'''
  s+=f'end AspisR1.JFw_TX2_{name}\nend\n';emit(f'lean/JFw_TX2_{name}.lean',s)
 mod=f'JFw_TX2_Head{slot}'
 s=''.join(f'import JFw_TX2_{name}\n' for name in names)+f'''import JFw_TX2_Coefficients
import JFw_TX2_CellUnique
set_option autoImplicit false
noncomputable section
namespace AspisR1.{mod}
open Aeneas Aeneas.Std Result
open JFv_TX2_ArrayMeaning (cell)
def value : FIo_Install.NE := {rec(nums)}
'''
 for j in range(8):
  name=('Head00' if j==0 else 'Head0Lo' if j<4 else 'Head0Hi') if slot==0 else f'Head{slot}'+('Lo' if j<4 else 'Hi')
  s+=f'theorem lane{j} : JFv_TX2_InnerMeaning.sum 0 {slot} {j} 0 26%2147483647={nums[j]} := JFw_TX2_{name}.lane{j}\n'
 s+=f'''theorem source : JFs_TX2_ScalarHead.sourceCall
    (JFr_TX2_Windows.array (JFn_Values.position 0)) JFr_TX2_FirstLane.native {slot}#usize=ok value := by
  obtain ⟨out,run,_,h⟩ := JFv_TX2_HeadFlat.source 0 {slot}
  have same : out=value := JFw_TX2_CellUnique.source out value (by
    intro j
    fin_cases j
'''
 for j in range(8):s+=f'    · exact (h {j}).trans lane{j}\n'
 s+='    )\n  exact same ▸ run\n'
 for j in range(8):s+=f'#print axioms lane{j}\n'
 s+=f'#print axioms source\nend AspisR1.{mod}\nend\n';emit(f'lean/{mod}.lean',s)
emit('evidence/fixture-tx2g-20261026/JFw_HEADS.json',json.dumps(heads,indent=2)+'\n')
