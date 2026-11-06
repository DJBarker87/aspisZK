from pathlib import Path
import json
E=Path(__file__).resolve().parent;rows=json.loads((E/'NLC_STEP_PLAN.json').read_text())
prefix='\n'.join('import '+x['module'] for x in rows)+'''
import NLC_FrameAlgebra
set_option autoImplicit false
noncomputable section
namespace AspisR1.NLC_Finish
open Aeneas Aeneas.Std Result AspisR1PublicPreparation
/-- Source order, with nested callback markers excluded from normal dispatch. -/
def rank : Event → Nat
'''
for n,x in enumerate(rows):prefix+=f' | .{x["site"]} => {n}\n'
prefix+=''' | .lowIndex => 32
 | .highIndex => 33

def RankPost {H : Type} (s : State H) : Post H → Prop
 | .inl _ => True
 | .inr after => rank after.next = rank s.next + 1

theorem rank_put {H : Type} (s : State H) (e : Event) (l : Locals H)
 (order : rank e = rank s.next + 1) : RankPost s (.inr (put s e l)) := order

theorem rank_next {H : Type} (s : State H) (e : Event)
 (order : rank e = rank s.next + 1) : RankPost s (.inr (setNext s e)) := order

theorem rank_returned {A H : Type} (s : State H) (e : Event)
 (r : core.result.Result A r1_wire.Error) (store : A → Locals H)
 (order : rank e = rank s.next + 1) : RankPost s (returned s e r store) := by
 cases r with
 | Ok a => exact order
 | Err e => trivial
'''
for x in rows:
 name=x['site'];prefix+='''
/-- Every possible returning reply advances exactly one source state. -/
theorem rank_NAME {H : Type} (s : State H) (atSite : s.next = .NAME) :
 AllLeaves (RankPost s) (step s) := by
 rw [step_NAME s atSite]
 unfold window_NAME
 repeat' first
 | (apply all_bind; intro)
 | (change ∀ _, _; intro)
 | (apply rank_returned; rw [atSite]; rfl)
 | (apply rank_put; rw [atSite]; rfl)
 | (apply rank_next; rw [atSite]; rfl)
 | (change True; trivial)
 | split
#print axioms rank_NAME
'''.replace('NAME',name)
prefix+='''
theorem rank_bound (e : Event) : rank e < 34 := by cases e <;> decide
#print axioms rank_put
#print axioms rank_next
#print axioms rank_returned
#print axioms rank_bound
end AspisR1.NLC_Finish
end
'''
(E/'NLC_generated/NLC_Rank.lean').write_text(prefix)
print('Generated bounded chronological progression laws')
# Split the symbolic progression proof before compiling: no whole32-theorem job.
all_text=prefix
begin=all_text.index('/-- Source order')
first=all_text.index('/-- Every possible returning reply')
bound=all_text.index('theorem rank_bound')
base='''import NLC_FrameAlgebra
set_option autoImplicit false
noncomputable section
namespace AspisR1.NLC_Finish
open Aeneas Aeneas.Std Result AspisR1PublicPreparation
'''+all_text[begin:first]+all_text[bound:]
(E/'NLC_generated/NLC_RankBase.lean').write_text(base)
blocks=all_text[first:bound].split('/-- Every possible returning reply')
chunks=[]
for idx in range(4):
 chosen=rows[idx*8:(idx+1)*8]
 text='\n'.join('import '+x['module'] for x in chosen)+'''\nimport NLC_RankBase
set_option autoImplicit false
noncomputable section
namespace AspisR1.NLC_Finish
open Aeneas Aeneas.Std Result AspisR1PublicPreparation
'''
 for b in blocks[1+idx*8:1+(idx+1)*8]:text+='/-- Every possible returning reply'+b
 text+='end AspisR1.NLC_Finish\nend\n'
 mod='NLC_Rank'+str(idx)
 (E/'NLC_generated'/(mod+'.lean')).write_text(text);chunks.append(mod)
(E/'NLC_generated/NLC_Rank.lean').write_text('\n'.join('import '+m for m in chunks)+'\n')
