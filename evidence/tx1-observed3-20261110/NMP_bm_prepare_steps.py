from pathlib import Path
import re
E=Path(__file__).resolve().parent
s=(E/'NMP_PrepareState.lean').read_text();start=s.index('def step');end=s.index('\ndef execute',start);body=s[start:end]
parts=list(re.finditer(r'^ \| \.(\w+) (.*?) => do\n',body,re.M));assert len(parts)==8
args=['','(logical : alloc.vec.Vec U8)','(semantic y1 : Slice U8) (back : SplitBack) (vecBack : VecBack)','(semantic y1 : Slice U8) (back : SplitBack) (vecBack : VecBack)','(semantic y1 : Slice U8)','(v : verifier.View)','(v : verifier.View) (sem : r1_semantic.Verified H)','(v : verifier.View) (sem : r1_semantic.Verified H)']
for i,m in enumerate(parts):
 b=body[m.end():parts[i+1].start() if i+1<len(parts) else len(body)].rstrip()
 text='''import NMP_PrepareState
set_option autoImplicit false
noncomputable section
namespace AspisR1.NMP_PrepareSteps
open Aeneas Aeneas.Std Result NMP_prepare NMP_Emitted
open NMT_CallTree (Code invoke erase)
'''+f'''/-- Source occurrence{i}: {m[1]}; complete reply and writeback at SAME arguments. -/
theorem occurrence{i} {{H W : Type}} (c : Calls) (s : Parent H W) {args[i]} :
 step c (.{m[1]} {m[2]}) = (do
'''+b+f''') := rfl
#print axioms occurrence{i}
end AspisR1.NMP_PrepareSteps
'''
 (E/f'NMP_PrepareStep{i}.lean').write_text(text)
print('Drafted eight prepare occurrence modules')
