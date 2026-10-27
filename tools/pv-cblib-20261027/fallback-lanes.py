"""Generate symbolic four-lane helper normal forms, never concrete SHA reduction."""
from pathlib import Path
root=Path(__file__).resolve().parents[2];b=root/'docs/research/v8-r0-zk-20261009/lean/R1Z'
base='''import R1Z.PV_CBL_FallbackSchedule
import R1Z.PV_CBL_FallbackArray4
open Aeneas Aeneas.Std Result
namespace R1Z.PV_CBL_FallbackLane%s
open PV_CBL_FallbackArray4
set_option autoImplicit false
'''
ops={'Or':'a ||| b','Xor':'a ^^^ b','Add':'U32.wrapping_add a b'}
for name,op in ops.items():
 fn=name.lower();vars='(a0 a1 a2 a3 b0 b1 b2 b3 : U32)'
 vals=' '.join('('+op.replace('a',f'a{i}').replace('b',f'b{i}')+')' for i in range(4)) if name!='Add' else ' '.join(f'(U32.wrapping_add a{i} b{i})' for i in range(4))
 s=base%name+f'''theorem shape {vars} :
    PV_CBL_FallbackSchedule.sha_fallback_reference.{fn}
      (pack a0 a1 a2 a3) (pack b0 b1 b2 b3) =
      ok (pack {vals}) := by
  simp only [PV_CBL_FallbackSchedule.sha_fallback_reference.{fn},index0,index1,index2,index3,lift,bind_tc_ok]
  rfl
#print axioms shape
end R1Z.PV_CBL_FallbackLane{name}
'''
 (b/f'PV_CBL_FallbackLane{name}.lean').write_text(s)
for name,fn,op in [('Right','shl','wrapping_shr'),('Left','shr','wrapping_shl')]:
 vals=' '.join(f'(U32.{op} a{i} o)' for i in range(4))
 s=base%name+f'''theorem shape (a0 a1 a2 a3 o : U32) :
    PV_CBL_FallbackSchedule.sha_fallback_reference.{fn} (pack a0 a1 a2 a3) o =
      ok (pack {vals}) := by
  simp only [PV_CBL_FallbackSchedule.sha_fallback_reference.{fn},index0,index1,index2,index3,lift,bind_tc_ok]
  rfl
#print axioms shape
end R1Z.PV_CBL_FallbackLane{name}
''';(b/f'PV_CBL_FallbackLane{name}.lean').write_text(s)
s=base%'Load'+'''theorem shape (a0 a1 a2 a3 b0 b1 b2 b3 : U32) :
    PV_CBL_FallbackSchedule.sha_fallback_reference.sha256load
      (pack a0 a1 a2 a3) (pack b0 b1 b2 b3) = ok (pack b3 a0 a1 a2) := by
  simp only [PV_CBL_FallbackSchedule.sha_fallback_reference.sha256load,index0,index1,index2,index3,lift,bind_tc_ok]
  rfl
#print axioms shape
end R1Z.PV_CBL_FallbackLaneLoad
''';(b/'PV_CBL_FallbackLaneLoad.lean').write_text(s)
