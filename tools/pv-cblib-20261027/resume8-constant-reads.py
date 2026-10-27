from pathlib import Path
import sys
b=Path(__file__).resolve().parents[2]/'docs/research/v8-r0-zk-20261009/lean/R1Z'
for i in range(16):
 n=f'PV_CBL_BlockConstantRead{i:02}'
 s=f'''import R1Z.PV_CBL_FallbackConstantMatrix
import R1Z.PV_CBL_FallbackArrayRead
open Aeneas Aeneas.Std Result
namespace R1Z.{n}
set_option autoImplicit false
theorem source : Array.index_usize PV_CBL_FallbackConstantMatrix.matrix {i}#usize =
    ok PV_CBL_FallbackConstantMatrix.q{i} := by
  simp [Array.index_usize,Array.getElem?_Usize_eq,PV_CBL_FallbackConstantMatrix.matrix]
#print axioms source
end R1Z.{n}
'''
 p=b/(n+'.lean')
 if '--check' in sys.argv:assert p.read_text()==s
 else:p.write_text(s)
print('constant reads',16)
