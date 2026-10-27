from pathlib import Path
P=Path(__file__).resolve().parent;R=P.parents[1]
s=(R/'evidence/fixture-tx2m-20261027/JGm_level_join.py').read_text()
s=s.replace('JGm_TX2_Levels','JGu_Levels').replace('JGm_TX2_Level','JGu_Level')
s=s.replace('JGm_TX2_Supplied','JGu_Supplied').replace('JGk_TX2_Scratch','JGu_Scratch').replace('s12','s10')
s=s.replace('JGm_TX2_Initial{t}','JGu_Initial{t}').replace('import JGm_TX2_Initial','import JGu_Initial{t}')
s=s.replace('5216 if t<2 else 4512','4416 if t<2 else 3840')
exec(compile(s,str(P/'JGu_joins_emitter'),'exec'),globals())
(P/'JGu_joins_generated.lean.txt').write_text(s)
# Append the finite native index scan and owned verifier in the same tree-local
# compilation unit; preserve one tree's imports and exact returned output.
import re
old=(R/'lean/JGm_TX2_Verify.lean').read_text()
for t in range(3):
 level=f'JGu_Level{t}_00';ns=f'JGu_Valid{t}'
 text=(R/f'lean/{level}.lean').read_text()
 inds=[int(x) for x in re.search(r'def indices00 : List U32 := \[(.*?)\]',text)[1].replace('#u32','').split(',')]
 add=f'''set_option autoImplicit false
noncomputable section
namespace AspisR1.{ns}
open Aeneas Aeneas.Std Result MultiproofConeRef
 theorem source (s : reference.Scratch)
    (view : JGm_TX2_View.View s {level}.indices00 {level}.values00 0) :
    reference.valid_indices s.idx 10#usize 0#usize=ok true := by
'''
 for j,x in enumerate(inds):
  add+=f'''  have r{j:02} : Array.index_usize s.idx {j}#usize=ok {x}#u32 :=
    JGm_TX2_View.index s {level}.indices00 {level}.values00 0 view {j}#usize (by decide)
'''
 add+='  calc\n'
 for j,x in enumerate(inds):
  lhs='reference.valid_indices s.idx 10#usize 0#usize' if j==0 else '_'
  add+=f'''    {lhs}=reference.valid_indices s.idx 10#usize {j+1}#usize := by
      rw [reference.valid_indices,if_neg (by decide : ¬{j}#usize≥10#usize),r{j:02}]
      simp only [bind_tc_ok]
      rw [if_neg (by decide : ¬{x}#u32≥262144#u32)]
'''
  if not j:add+='      rw [if_neg (by decide : ¬0#usize>0#usize)]\n'
  else:add+=f'''      rw [if_pos (by decide : {j}#usize>0#usize),JGm_TX2_Scalar.sub {j}#usize 1#usize {j-1}#usize (by decide) rfl,bind_tc_ok,r{j-1:02},bind_tc_ok,
        if_neg (by decide : ¬{inds[j-1]}#u32≥{x}#u32)]
'''
  add+=f'      rw [JGm_TX2_Scalar.add {j}#usize 1#usize {j+1}#usize rfl]\n      rfl\n'
 add+='''    _=ok true := by rw [reference.valid_indices,if_pos (by decide : 10#usize≥10#usize)]
#print axioms source
'''
 add+=f'''theorem on_scratch (s : reference.Scratch) :
    reference.valid_indices (JGu_Scratch{t}.s10 s).idx 10#usize 0#usize=ok true :=
  source _ (JGu_Initial{t}.source s)
#print axioms on_scratch
end AspisR1.{ns}
end
'''
 sec=old[old.index(f'namespace AspisR1.JGm_TX2_Verify{t}'):]
 sec=sec[:sec.index(f'end AspisR1.JGm_TX2_Verify{t}')]+f'end AspisR1.JGm_TX2_Verify{t}\nend\n'
 sec=sec.replace('4512','3840')
 for i,prefix,last in [(0,'JGf',185),(1,'JGh',185),(2,'JGc',163)]:
  sec=sec.replace(f'{prefix}_TX2_M{i}Root',f'JGr_M{i}Root')
  if t==i:sec=sec.replace(f'value{last:03}',f'value{156 if t<2 else 138:03}')
 sec=sec.replace('JGm_TX2_Verify','JGu_Verify').replace('JGm_TX2_Levels','JGu_Levels').replace('JGm_TX2_Valid','JGu_Valid').replace('JGm_TX2_Supplied','JGu_Supplied').replace('JGk_TX2_Scratch','JGu_Scratch').replace('s12','s10').replace('12#usize','10#usize').replace('5216','4416').replace('4512','3840')
 add+='set_option autoImplicit false\nnoncomputable section\n'+sec
 target=R/f'lean/JGu_Levels{t}.lean';base=target.read_text();target.write_text(base+add)
print('Added exact index scans and native owned-verifier compositions')
