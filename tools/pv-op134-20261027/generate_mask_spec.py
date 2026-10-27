from pathlib import Path
import sys
root=Path(__file__).resolve().parents[2];lean=root/'docs/research/v8-r0-zk-20261009/lean/R1Z'
s=''.join(f'import R1Z.PV_Op134_MaskBits{i}\n' for i in range(8))
s+='''import R1Z.PV_Op134_RowOrder
namespace R1Z.PV_Op134_MaskSpec
open Aeneas Aeneas.Std
set_option autoImplicit false

theorem bits (block : Fin 64) (bit : Fin 16) :
    Nat.testBit (PV_Op134_Masks.masks.val[block.val]'(by
      rw [PV_Op134_Masks.length]; exact block.isLt)).val bit.val = true ↔
      16*block.val+bit.val ∈ PV_Op134_RowSpec.rows.map (fun r => r.val) := by
  have hb := block.isLt
'''
for i in range(7):
 s+='  '* (i+1)+f'by_cases h{i} : block.val < {8*(i+1)}\n'
 s+='  '* (i+1)+f'· let j : Fin 8 := ⟨block.val-{8*i},by omega⟩\n'
 s+='  '* (i+2)+f'have he : {8*i}+j.val=block.val := by dsimp [j]; omega\n'
 s+='  '* (i+2)+f'simpa only [he] using PV_Op134_MaskBits{i}.bits j bit\n'
 s+='  '* (i+1)+'·\n'
s+='  '*8+'let j : Fin 8 := ⟨block.val-56,by omega⟩\n'
s+='  '*8+'have he : 56+j.val=block.val := by dsimp [j]; omega\n'
s+='  '*8+'simpa only [he] using PV_Op134_MaskBits7.bits j bit\n'
s+='''
#print axioms bits
end R1Z.PV_Op134_MaskSpec
'''
p=lean/'PV_Op134_MaskSpec.lean'
if '--check' in sys.argv:assert p.read_text()==s
else:p.write_text(s)
print('CHECK' if '--check' in sys.argv else 'GENERATED','mask composition')
