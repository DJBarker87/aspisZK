from pathlib import Path
R=Path(__file__).resolve().parents[2]
for t in range(3):
 ns=f'JGm_TX2_Initial{t}'
 s=f'''import JGm_TX2_View
import JGm_TX2_Level{t}_00
import JGk_TX2_ScratchIndices
set_option autoImplicit false
noncomputable section
namespace AspisR1.{ns}
open Aeneas Aeneas.Std Result MultiproofConeRef
open AspisV8R19.SqueezeOracleBridge
'''
 # Reuse inherited actual native leaf push states; only derive their value prefix.
 cur=[]
 import re
 text=(R/f'lean/JGk_TX2_Scratch{t}.lean').read_text()
 found=re.findall(r'JGk_TX2_LeafPush.push \(s(\d+) s\) (\d+)#u32 \(encodeState \((.*?)\)\)',text)
 assert len(found)==12,(t,len(found))
 for j,(_,key,value) in enumerate(found):
  cur.append('encodeState ('+value+')')
  s+=f'''theorem values{j+1:02} (s : reference.Scratch) :
    (JGk_TX2_Scratch{t}.s{j+1:02} s).val.val.take {j+1}=[{','.join(cur)}] := by
  change ((JGk_TX2_Scratch{t}.s{j:02} s).val.set (JGk_TX2_Scratch{t}.s{j:02} s).n (encodeState ({value}))).val.take {j+1}=_
  rw [Array.set_val_eq]
  change ((JGk_TX2_Scratch{t}.s{j:02} s).val.val.set {j} (encodeState ({value}))).take ({j}+1)=_
  rw [JGk_TX2_ScratchIndices.snoc_set _ _ _ (by
    have len : (JGk_TX2_Scratch{t}.s{j:02} s).val.val.length=16 := (JGk_TX2_Scratch{t}.s{j:02} s).val.property
    omega)]
'''
  if j:s+=f'  rw [values{j:02}]\n'
  s+=f'  rfl\n#print axioms values{j+1:02}\n'
 s+=f'''theorem source (s : reference.Scratch) :
    JGm_TX2_View.View (JGk_TX2_Scratch{t}.s12 s) JGm_TX2_Level{t}_00.indices00 JGm_TX2_Level{t}_00.values00 0 := by
  refine ⟨rfl,rfl,?_,?_,rfl⟩
  · exact JGk_TX2_ScratchIndices.front{t}_12 s
  · exact values12 s
#print axioms source
end AspisR1.{ns}
end
'''
 (R/f'lean/{ns}.lean').write_text(s)
print('Generated native initial prefix views')
