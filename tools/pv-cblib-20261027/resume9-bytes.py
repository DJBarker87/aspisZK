from pathlib import Path
import sys
p=Path('docs/research/v8-r0-zk-20261009/lean/R1Z')
for k in range(16):
 name=f'PV_CBL_ByteLane{k:02}'
 s=f'''import R1Z.PV_CBL_ByteLoadSource
open Aeneas Aeneas.Std Result
namespace R1Z.{name}
set_option autoImplicit false
def value (b : Array U8 64#usize) : U32 :=
  PV_CBL_ByteCodecValue.load '''+' '.join(f'b.val[{4*k+j}]!' for j in range(4))+f'''
theorem source (b : Array U8 64#usize) :
    PV_CBL_ShaBytes.sha_load_lane{k} b = ok (value b) := by
  unfold PV_CBL_ShaBytes.sha_load_lane{k}
'''
 for j in range(4): s+=f'  rw [PV_CBL_ArrayReadValue.read b {4*k+j}#usize (by decide),bind_tc_ok]\n'
 s+='  rw [PV_CBL_ByteLoadSource.source]\n  rfl\n#print axioms value\n#print axioms source\nend R1Z.'+name+'\n'
 q=p/f'{name}.lean'
 if '--check' in sys.argv: assert q.read_text()==s
 else: q.write_text(s)
