"""Bounded 32-byte parser cells; no recurrence or whole-prefix reduction."""
from pathlib import Path
import re
root=Path(__file__).resolve().parents[2]
text='\n'.join(p.read_text() for p in sorted((root/'lean').glob('JGe_Window27_*.lean')))
for i in range(29):
 c=f'c{i:02}'
 m=re.search(r'def '+c+r' : List U8 := \[([^\]]*)\]',text)
 vals=[int(n) for n in re.findall(r'(\d+)#u8',m.group(1))]+[0]*16
 assert len(vals)==32
 s=f'''import JGi_FieldCell
import JGi_FieldWindows
set_option autoImplicit false
namespace AspisR1.JGi_Y1Cell{i:02}
open Aeneas Aeneas.Std Result AspisR1CurrentPreparedClaim
open AspisR1.ExtractedRecordByteCanonicality
def arr : Array U8 32#usize := Array.make 32#usize [{','.join(str(v)+'#u8' for v in vals)}]
theorem selected : (JGe_Payload27.value.val.drop (32*{i})).take 32=arr.val := by
  rw [JGi_FieldWindows.selected {i} (by decide)]
  rfl
#print axioms selected
'''
 for j in range(8):
  n=int.from_bytes(bytes(vals[4*j:4*j+4]),'little');assert n<2147483647
  s+=f'theorem word{j} : wordLE arr {j}={n}#u32 := by rfl\n#print axioms word{j}\n'
 s+='''theorem bounds : ∀ j : Fin 8,(wordLE arr j).val<2147483647 := by
  intro j
  fin_cases j
'''
 for j in range(8):s+=f'  · change (wordLE arr {j}).val<2147483647\n    rw [word{j}];scalar_tac\n'
 s+=f'''#print axioms bounds
theorem source : ∃ out,ClaimParser.field JGe_Payload27.value {i}#usize=ok out ∧ Concrete.Canonical out := by
  exact JGi_FieldCell.source _ _ arr (by rw [JGe_Payload27.length];decide)
    (by rw [JGe_Payload27.length];decide) selected bounds
#print axioms source
end AspisR1.JGi_Y1Cell{i:02}
'''
 (root/'lean'/f'JGi_Y1Cell{i:02}.lean').write_text(s)
