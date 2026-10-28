from pathlib import Path
import sys
def emit(p,s):
 if "--check" in sys.argv:
  assert p.read_text()==s,str(p)
 else:p.write_text(s)
P=Path(__file__).resolve().parent; R=P.parents[1]
groups=[('Query','JHk_PreparedRemaining',320,4,22,lambda i:f'JFq_QueryWords.b{i}.val',lambda i:f'JFq_QueryWords.select{i}'),('Semantic','JHl_SemanticBytes',408,16,10,lambda i:f'JFq_Sem{i:02}.bytes',lambda i:f'JFq_Sem{i:02}.selected'),('Z','JHl_ZBytes',568,16,4,lambda i:f'JFq_Z{i}.bytes',lambda i:f'JFq_Z{i}.selected')]
for name,imp,off,n,count,term,law in groups:
 expr=' ++ '.join(term(i) for i in range(count))
 src=f'''import {imp}
import JHn_Ranges
set_option autoImplicit false
namespace AspisR1.JHn_{name}Ranges
open Aeneas Aeneas.Std
attribute [local irreducible] JFx_NativeBytes.checkpoint JFx_NativeBytes.checkpointBytes
theorem source : {expr} =
    (JFx_NativeBytes.checkpoint.val.drop {off}).take {n*count} := by
  rw [{','.join('←'+law(i) for i in range(count))}]
  rw [{','.join(f'JHn_Ranges.adjacent _ {off} {n*i} {n}' for i in range(1,count))}]
#print axioms source
end AspisR1.JHn_{name}Ranges
'''
 emit(R/'lean'/f'JHn_{name}Ranges.lean',src)
