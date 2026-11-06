from pathlib import Path
E=Path(__file__).resolve().parent
s='''import NKK_RawPrefix
import NKK_LogAlgebra
import NKK_LogReduce
set_option autoImplicit false
noncomputable section
namespace NKK_QueryStage
open Aeneas Aeneas.Std Result NKK_NativeRaw
open AspisR1 NID_ResumeEmission NJU_ResumeObserved
'''
for count in [8,6]:
 s+=f'\ndef source{count} (r : Reader) : NJU_Log.Run Event (List U32 × Reader) := do\n'
 for i in range(count):s+=f' let (b{i},r{i+1}) ← recordRaw 4#usize '+('r' if i==0 else f'r{i}')+'\n'
 s+=' pure (['+','.join(f'core.num.U32.from_le_bytes b{i}' for i in range(count))+f'],r{count})\n'
 s+=f'''\ndef model{count} (r : Reader) : NJU_Log.Run Event (List U32 × Reader) := do
 let (bs,next) ← NKK_RawPrefix.literal 4#usize {count} r
 pure (bs.map core.num.U32.from_le_bytes,next)

theorem stage{count} (r : Reader) : model{count} r=source{count} r := by
 unfold model{count} source{count}
 simp only [NKK_RawPrefix.literal,NKK_LogAlgebra.bind_assoc,NKK_LogAlgebra.pure_bind,
  List.map_cons,List.map_nil,NJU_Log.prod_cases]

#print axioms stage{count}
'''
s+='end NKK_QueryStage\n';E.joinpath('NKK_QueryStage.lean').write_text(s)
