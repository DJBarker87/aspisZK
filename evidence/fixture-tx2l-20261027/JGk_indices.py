from pathlib import Path
import re
R=Path(__file__).resolve().parents[2]
p=R/'lean/JGk_TX2_SiblingBase.lean'
p.write_text('''import JGk_TX2_FrontierOrder0
import JGk_TX2_FrontierOrder2
set_option autoImplicit false
namespace AspisR1.JGk_TX2_SiblingBase
open AspisV8R19.SourceDuplexStep
'''+''.join(f'''def native{t} (h b : Nat) : State := JGh_TX2_NodeViews.readCell JGh_TX2_NodeViews.nodes{t}
  (JGk_TX2_Group{2 if t==2 else 0}_00.stream.idxOf (h,b))
''' for t in range(3))+'''end AspisR1.JGk_TX2_SiblingBase
''')
groups={}
for tree in [0,2]:
 for h in range(18):
  s=(R/f'lean/JGk_TX2_Group{tree}_{h:02}.lean').read_text()
  groups[tree,h]=[(int(a),int(b)) for a,b in re.findall(r'\((\d+),(\d+)\)',re.search('def group.* := (.*)',s)[1])]
for h in range(18):
 ns=f'JGk_TX2_Lookup{h:02}'
 s=f'''import JGk_TX2_SiblingBase
set_option autoImplicit false
namespace AspisR1.{ns}
open AspisV8R19.SourceDuplexStep
attribute [local irreducible] JGh_TX2_NodeViews.nodes0 JGh_TX2_NodeViews.nodes1 JGh_TX2_NodeViews.nodes2
'''
 for tree in [0,2]:
  if not groups[tree,h]:continue
  offset=sum(len(groups[tree,j]) for j in range(h))
  g=f'JGk_TX2_Group{tree}_{h:02}'
  s+=f'''theorem offset{tree} (b : Nat) (hb : ({h},b) ∈ {g}.group) :
    JGk_TX2_Group{tree}_00.stream.idxOf ({h},b)={offset}+{g}.group.idxOf ({h},b) := by
'''
  for j in range(h):
   prev=f'JGk_TX2_Group{tree}_{j:02}'
   s+=f'''  rw [{prev}.stream,List.idxOf_append_of_notMem (show ({h},b) ∉ {prev}.group from by
    intro hm
    have e := {prev}.height ({h},b) hm
    contradiction)]
'''
  s+=f'  rw [{g}.stream,List.idxOf_append_of_mem hb]\n'
  if h:
   s+='  simp only ['+','.join(f'show JGk_TX2_Group{tree}_{j:02}.group.length={len(groups[tree,j])} from rfl' for j in range(h))+']\n  all_goals omega\n'
  else:s+='  simp only [Nat.zero_add]\n'
  s+=f'#print axioms offset{tree}\n'
 for tree in range(3):
  gt=2 if tree==2 else 0
  model={0:'JGf_TX2_M0Roots',1:'JGh_TX2_M1Roots',2:'JGc_TX2_M2Roots'}[tree]
  pairs=groups[gt,h]
  s+=f'''theorem source{tree} (b : Nat) (hb : b ∈ {model}.bases {h}) :
    JGk_TX2_SiblingBase.native{tree} {h} b={model}.siblingAt {h} b := by
  simp only [{model}.bases,List.mem_cons,List.not_mem_nil,or_false] at hb
'''
  if not pairs:s+='  all_goals contradiction\n'
  else:
   s+='  rcases hb with '+'|'.join('rfl' for _ in pairs)+'\n'
   for j,(_,b) in enumerate(pairs):
    offset=sum(len(groups[gt,k]) for k in range(h))
    s+=f'''  · unfold JGk_TX2_SiblingBase.native{tree}
    rw [offset{gt} {b} (by decide)]
    rw [show JGk_TX2_Group{gt}_{h:02}.group.idxOf ({h},{b})={j} from rfl]
    exact JGh_TX2_Siblings{h:02}.k{tree}c{offset+j:03}_read
'''
  s+=f'#print axioms source{tree}\n'
 s+=f'end AspisR1.{ns}\n'
 (R/f'lean/{ns}.lean').write_text(s)
