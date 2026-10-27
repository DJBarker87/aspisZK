from pathlib import Path
import sys
p=Path('docs/research/v8-r0-zk-20261009/lean/R1Z')
s='''import R1Z.PV_CBL_ShaPadFixed
import R1Z.PV_CBL_ArrayReadValue
import R1Z.PV_CBL_ArrayStep
open Aeneas Aeneas.Std Result
namespace R1Z.PV_CBL_PadSuffixValue
set_option autoImplicit false
def value (out : Array U8 64#usize) (suffix : Array U8 8#usize) : Array U8 64#usize :=
'''
e='out'
for i in range(8):e=f'({e}.set {56+i}#usize suffix.val[{i}]!)'
s+='  '+e+'\n'
s+='''theorem source (out : Array U8 64#usize) (suffix : Array U8 8#usize) :
    PV_CBL_ShaPadFixed.sha_pad_suffix8 out suffix = ok (value out suffix) := by
  unfold PV_CBL_ShaPadFixed.sha_pad_suffix8
'''
for i in range(8):s+=f'  rw [PV_CBL_ArrayReadValue.read suffix {i}#usize (by decide),bind_tc_ok]\n'

for i in range(8):s+=f'  rw [PV_CBL_ArrayStep.write _ {56+i}#usize _ (by decide)'+(',bind_tc_ok' if i<7 else '')+']\n'
s+='  rfl\n#print axioms value\n#print axioms source\nend R1Z.PV_CBL_PadSuffixValue\n'
q=p/'PV_CBL_PadSuffixValue.lean'
if '--check' in sys.argv: assert q.read_text()==s
else: q.write_text(s)
