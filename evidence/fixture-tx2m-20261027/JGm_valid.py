import sys
from pathlib import Path
import re
R=Path(__file__).resolve().parents[2]
for t in range(3):
 ns=f'JGm_TX2_Valid{t}'
 level=f'JGm_TX2_Level{t}_00'
 text=(R/f'lean/{level}.lean').read_text()
 inds=[int(x) for x in re.search(r'def indices00 : List U32 := \[(.*?)\]',text)[1].replace('#u32','').split(',')]
 s=f'''import JGm_TX2_Initial{t}
import JGm_TX2_Scalar
set_option autoImplicit false
noncomputable section
namespace AspisR1.{ns}
open Aeneas Aeneas.Std Result MultiproofConeRef
 theorem source (s : reference.Scratch)
    (view : JGm_TX2_View.View s {level}.indices00 {level}.values00 0) :
    reference.valid_indices s.idx 12#usize 0#usize=ok true := by
'''
 for j,x in enumerate(inds):
  s+=f'''  have r{j:02} : Array.index_usize s.idx {j}#usize=ok {x}#u32 :=
    JGm_TX2_View.index s {level}.indices00 {level}.values00 0 view {j}#usize (by decide)
'''
 s+='  calc\n'
 for j,x in enumerate(inds):
  lhs='reference.valid_indices s.idx 12#usize 0#usize' if j==0 else '_'
  s+=f'''    {lhs}=reference.valid_indices s.idx 12#usize {j+1}#usize := by
      rw [reference.valid_indices,if_neg (by decide : ¬{j}#usize≥12#usize),r{j:02}]
      simp only [bind_tc_ok]
      rw [if_neg (by decide : ¬{x}#u32≥262144#u32)]
'''
  if j==0:s+='      rw [if_neg (by decide : ¬0#usize>0#usize)]\n'
  else:
   s+=f'''      rw [if_pos (by decide : {j}#usize>0#usize),JGm_TX2_Scalar.sub {j}#usize 1#usize {j-1}#usize (by decide) rfl,bind_tc_ok,r{j-1:02},bind_tc_ok,
        if_neg (by decide : ¬{inds[j-1]}#u32≥{x}#u32)]
'''
  s+=f'      rw [JGm_TX2_Scalar.add {j}#usize 1#usize {j+1}#usize rfl]\n      rfl\n'
 s+='''    _=ok true := by rw [reference.valid_indices,if_pos (by decide : 12#usize≥12#usize)]
#print axioms source
'''
 s+=f'''theorem on_scratch (s : reference.Scratch) :
    reference.valid_indices (JGk_TX2_Scratch{t}.s12 s).idx 12#usize 0#usize=ok true :=
  source _ (JGm_TX2_Initial{t}.source s)
#print axioms on_scratch
end AspisR1.{ns}
end
'''
 out=R/f'lean/{ns}.lean'
 if '--check' in sys.argv: assert out.read_text()==s,ns
 else: out.write_text(s)
print('Generated three actual native index scans')
