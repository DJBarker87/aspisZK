from pathlib import Path
R=Path(__file__).resolve().parents[2]
values=[14297,21248,42158,55377,63860,132355,149624,166165,178080,179622,185637,218094]
s=''.join(f'import JGk_TX2_Scratch{t}\n' for t in range(3))+'''set_option autoImplicit false
namespace AspisR1.JGk_TX2_ScratchIndices
open Aeneas Aeneas.Std

theorem snoc_set {α : Type} (xs : List α) (i : Nat) (x : α) (bound : i<xs.length) :
    (xs.set i x).take (i+1)=xs.take i++[x] := by
  rw [List.take_succ_eq_append_getElem (by simpa only [List.length_set] using bound),List.take_set]
  rw [List.set_eq_of_length_le (by simp only [List.length_take];omega)]
  simp only [List.getElem_set_self]
#print axioms snoc_set
'''
for t in range(3):
 for i in range(1,13):
  vals=[x//4 if t==2 else x for x in values[:i]]
  model=f'JGk_TX2_Scratch{t}'
  raw='['+','.join(f'{x}#u32' for x in vals)+']'
  old=f'{model}.s{i-1:02} s'
  s+=f'''theorem front{t}_{i:02} (s : MultiproofConeRef.reference.Scratch) :
    ({model}.s{i:02} s).idx.val.take {i}={raw} := by
  change (({old}).idx.set ({old}).n {vals[-1]}#u32).val.take {i}=_
  rw [Array.set_val_eq]
  change (({old}).idx.val.set {i-1} {vals[-1]}#u32).take ({i-1}+1)=_
  rw [snoc_set _ _ _ (by have e : ({old}).idx.val.length=16 := ({old}).idx.property;omega)]
'''
  s+=f'  rw [front{t}_{i-1:02}]\n' if i>1 else ''
  s+='  rfl\n'+f'#print axioms front{t}_{i:02}\n'
s+='end AspisR1.JGk_TX2_ScratchIndices\n'
(R/'lean/JGk_TX2_ScratchIndices.lean').write_text(s)
