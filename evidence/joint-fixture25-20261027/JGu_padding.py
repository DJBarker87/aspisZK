from pathlib import Path
import re,json
P=Path(__file__).resolve().parent;R=P.parents[1]
exec((P/'JGu_generate.py').read_text().split("s='import JGm_TX2_Supplied")[0])
for t,row in enumerate(data):
 count=row['consumed']*32;start=row['slot_start'];cap=[146,146,128][t]*32
 ns=f'JGu_Padding{t}'
 s=f'''import JGp_Slot{t}
import JGk_TX2_ZeroWindows
set_option autoImplicit false
set_option linter.unusedSimpArgs false
namespace AspisR1.{ns}
open Aeneas Aeneas.Std Result
attribute [local irreducible] JFx_NativeBytes.proof
def padding : Slice U8 := Slice.drop JGp_Slot{t}.value {count}#usize
'''
 for j in range(8):
  s+=f'''theorem window{j} : (padding.val.drop {32*j}).take 32=List.replicate 32 0#u8 := by
  change (((JFw_Frames.window {start} {cap}).val.drop {count}).drop {32*j}).take 32=_
  rw [List.drop_drop,JFw_Frames.window,JFq_Range.nested _ _ _ _ _ (by decide)]
'''
  s+=selected(start+count+32*j,32,'List.replicate 32 0#u8')
  s+=f'#print axioms window{j}\n'
 s+=f'''theorem size : padding.val.length=256 := by
  change JGp_Slot{t}.value.val.length-{count}=256
  have len : JGp_Slot{t}.value.val.length={cap} := JGp_Slot{t}.length
  rw [len]
#print axioms size
theorem bytes : padding.val=List.replicate 256 0#u8 := by
  apply JGk_TX2_ZeroWindows.source 8 padding.val size
  intro i hi
  interval_cases i
'''
 for j in range(8):s+=f'  · exact window{j}\n'
 s+=f'#print axioms bytes\nend AspisR1.{ns}\n'
 (R/f'lean/{ns}.lean').write_text(s)
s=(R/'lean/JGm_TX2_PaddingScan.lean').read_text()
a=s.index('theorem source');s=s[a:s.index('end AspisR1.JGm_TX2_PaddingScan')]
s=s.replace('288','256').replace('8*36','8*32').replace('chunk_replicate','JGm_TX2_PaddingScan.chunk_replicate').replace('apply predicate D','apply JGm_TX2_PaddingScan.predicate D')
head='''import JGm_TX2_PaddingScan
import JGu_Padding0
import JGu_Padding1
import JGu_Padding2
set_option autoImplicit false
noncomputable section
namespace AspisR1.JGu_PaddingScan
open Aeneas Aeneas.Std Result
'''
s=head+s
old=(R/'lean/JGm_TX2_PaddingCalls.lean').read_text();a=old.index('theorem source');b=old.index('def padding0')
call=old[a:b].replace('theorem source','theorem calls').replace('288','256').replace('JGm_TX2_PaddingScan.source','source').replace('#print axioms source','#print axioms calls')
s+=call+'end AspisR1.JGu_PaddingScan\nend\n'
(R/'lean/JGu_PaddingScan.lean').write_text(s)
print('Generated three physical zero paddings and256-byte native scan')
