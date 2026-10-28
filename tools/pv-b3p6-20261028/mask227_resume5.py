"""Generate small, named symbolic laws for the seven reached u16 masks."""
from pathlib import Path
import json
D=Path('evidence/pv-b3p6-20261028');r=json.loads((D/'reference-copy227-resume5.json').read_text());masks=r['mask_specialization']['unique_masks'];allmasks=r['mask_specialization']['all64_masks']
s='''import Aeneas.Std
namespace PV_B3P_Mask227
set_option autoImplicit false

def trailing : Nat → Nat → Nat
  | 0, _ => 0
  | n+1, value => if value % 2 = 0 then 1 + trailing n (value / 2) else 0

def walk : Nat → Nat → List Nat
  | 0, _ => []
  | n+1, mask => if mask = 0 then [] else trailing 16 mask :: walk n (mask &&& (mask-1))

def popcount (mask : Nat) : Nat := ((List.range 16).filter (fun i => mask.testBit i)).length

'''
s+='''def foldResult {α : Type} (add : α → Nat → Aeneas.Std.Result α) : List Nat → α → Aeneas.Std.Result α
  | [], initial => .ok initial
  | index::tail, initial => do
    let next ← add initial index
    foldResult add tail next

'''
for mask in masks:
 bits=[i for i in range(16)if mask&(1<<i)];l='['+','.join(map(str,bits))+']'
 s+=f'theorem walk_{mask} : walk 16 {mask} = {l} := by decide\n'
 s+=f'theorem complement_off_{mask} : popcount {mask} ≤ 8 := by decide\n'
 chain='zero'
 for i in bits:chain=f'add ({chain}) (values {i})'
 s+=f'''theorem sum_{mask} {{α : Type}} (zero : α) (add : α → α → α) (values : Nat → α) :
    (walk 16 {mask}).foldl (fun sum index => add sum (values index)) zero = {chain} := by
  rw [walk_{mask}]
  rfl
'''
 chain='    do\n'
 prev='zero'
 for j,i in enumerate(bits):
  chain+=f'      let next{j} ← add {prev} {i}\n';prev=f'next{j}'
 chain+=f'      .ok {prev}'
 s+=f'theorem result_{mask} {{α : Type}} (zero : α) (add : α → Nat → Aeneas.Std.Result α) :\n    foldResult add (walk 16 {mask}) zero = ({chain}) := by\n  rw [walk_{mask}]\n  rfl\n'
 for n in ['walk','complement_off','sum','result']:s+=f'#print axioms {n}_{mask}\n'
s+='\ndef sourceMasks : List Nat := ['+','.join(map(str,allmasks))+']\n'
s+='def reachedMasks : List Nat := ['+','.join(map(str,masks))+']\n'
s+='''theorem table_masks : ∀ mask ∈ sourceMasks, mask ∈ reachedMasks := by decide
#print axioms table_masks
end PV_B3P_Mask227
'''
(D/'lean/PV_B3P_Mask227.lean').write_text(s)
