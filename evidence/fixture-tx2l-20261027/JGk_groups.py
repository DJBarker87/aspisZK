from pathlib import Path
import re
R=Path(__file__).resolve().parents[2]
s=(R/'evidence/fixture-tx2k-20261027/JGh_UNCHECKED/JGh_TX2_FrontierStream.lean.txt').read_text()
for tree in [0,2]:
 for h in range(17,-1,-1):
  ns=f'JGk_TX2_Group{tree}_{h:02}'
  g=re.search(rf'def group{tree}_{h:02} : List \(Nat×Nat\) := (.*)',s)[1]
  imp='JGk_TX2_OrderTools' if h==17 else f'JGk_TX2_Group{tree}_{h+1:02}'
  out=f'''import {imp}
set_option autoImplicit false
namespace AspisR1.{ns}
open JGk_TX2_OrderTools
def group : List (Nat × Nat) := {g}
theorem ordered : group.Pairwise le := by decide
#print axioms ordered
theorem height : ∀ x ∈ group, x.1={h} := by
  simp only [group,List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false]
  intro x hx
  rcases hx with '''
  pairs=re.findall(r'\((\d+),(\d+)\)',g)
  if not pairs:
   out=out[:out.index('  simp only')]+'''  intro x hx
  simp only [group,List.not_mem_nil] at hx
'''
  else:
   out+=' | '.join('hx' for _ in pairs)+'\n'
   out+='  all_goals subst x; rfl\n'
  out+='''#print axioms height
'''
  tail='[]' if h==17 else f'JGk_TX2_Group{tree}_{h+1:02}.stream'
  out+=f'def stream := group++{tail}\n'
  if h==17:
   out+='theorem stream_ordered : stream.Pairwise le := by\n  simpa only [stream,List.append_nil] using ordered\n'
   out+=f'theorem lower : ∀ x ∈ stream, {h}≤x.1 := by\n  intro x hx\n  have e:=height x (by simpa only [stream,List.append_nil] using hx)\n  omega\n'
  else:
   prev=f'JGk_TX2_Group{tree}_{h+1:02}'
   out+=f'''theorem stream_ordered : stream.Pairwise le := by
  apply append_groups {h} group {tail} ordered {prev}.stream_ordered height
  intro x hx
  have := {prev}.lower x hx
  omega
theorem lower : ∀ x ∈ stream, {h}≤x.1 := by
  intro x hx
  rcases List.mem_append.mp hx with hx|hx
  · have := height x hx; omega
  · have := {prev}.lower x hx; omega
'''
  out+='#print axioms stream_ordered\n#print axioms lower\nend AspisR1.'+ns+'\n'
  (R/'lean'/f'{ns}.lean').write_text(out)
