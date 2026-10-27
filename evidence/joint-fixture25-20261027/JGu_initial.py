from pathlib import Path
import re
P=Path(__file__).resolve().parent;R=P.parents[1]
for t in range(3):
 ns=f'JGu_Initial{t}'
 s=f'''import JGu_Scratch{t}
import JGu_Level{t}_00
import JGk_TX2_ScratchIndices
set_option autoImplicit false
noncomputable section
namespace AspisR1.{ns}
open Aeneas Aeneas.Std Result MultiproofConeRef
open AspisV8R19.SqueezeOracleBridge
'''
 text=(R/f'lean/JGu_Scratch{t}.lean').read_text()
 found=re.findall(r'JGk_TX2_LeafPush.push \(s(\d+) s\) (\d+)#u32 \(encodeState \((.*?)\)\)',text)
 assert len(found)==10
 for field in ['idx','val']:
  cur=[]
  for j,(_,key,value) in enumerate(found):
   term=key+'#u32' if field=='idx' else 'encodeState ('+value+')';cur.append(term)
   s+=f'''theorem {field}{j+1:02} (s : reference.Scratch) :
    (JGu_Scratch{t}.s{j+1:02} s).{field}.val.take {j+1}=[{','.join(cur)}] := by
  change ((JGu_Scratch{t}.s{j:02} s).{field}.set (JGu_Scratch{t}.s{j:02} s).n ({term})).val.take {j+1}=_
  rw [Array.set_val_eq]
  change ((JGu_Scratch{t}.s{j:02} s).{field}.val.set {j} ({term})).take ({j}+1)=_
  rw [JGk_TX2_ScratchIndices.snoc_set _ _ _ (by
    have len : (JGu_Scratch{t}.s{j:02} s).{field}.val.length=16 := (JGu_Scratch{t}.s{j:02} s).{field}.property
    omega)]
'''
   if j:s+=f'  rw [{field}{j:02}]\n'
   s+=f'  rfl\n#print axioms {field}{j+1:02}\n'
 s+=f'''theorem source (s : reference.Scratch) :
    JGm_TX2_View.View (JGu_Scratch{t}.s10 s) JGu_Level{t}_00.indices00 JGu_Level{t}_00.values00 0 := by
  refine ⟨rfl,rfl,?_,?_,rfl⟩
  · exact idx10 s
  · exact val10 s
#print axioms source
end AspisR1.{ns}
end
'''
 (R/f'lean/{ns}.lean').write_text(s)
