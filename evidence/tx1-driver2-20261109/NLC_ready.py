from pathlib import Path
import json
E=Path(__file__).resolve().parent;rows=json.loads((E/'NLC_STEP_PLAN.json').read_text())
slots=[('running',0),('alpha',0),('transcript',0),('claims',2),('terminalReply',4),('terminal',5),('low',7),('high',8),('blind',9),('mask',11),('record25',12),('extra',13),('product',14),('partialValue',15),('extraCell',16),('masked',17),('stateBefore',20),('z0',22),('record26',23),('beforeZ1',24),('z1',26),('payload',29),('root',30)]
text='''import NLC_RankBase
set_option autoImplicit false
noncomputable section
namespace AspisR1.NLC_Finish
open Aeneas Aeneas.Std Result AspisR1PublicPreparation
/-- Source slot initialization only. This says nothing about physical ownership,
canonicality, a successful child, or a native/source association. -/
def Ready {H : Type} (s : State H) : Prop :=
'''
text+=' ∧\n'.join(f' ({n} < rank s.next → s.locals.{name}.isSome = true)' for name,n in slots)+'\n'
text+='''
def ReadyPost {H : Type} : Post H → Prop
 | .inl _ => True
 | .inr after => Ready after

theorem ready_returned {A H : Type} (s : State H) (e : Event)
 (r : core.result.Result A r1_wire.Error) (store : A → Locals H)
 (initialized : ∀ a, Ready (put s e (store a))) : ReadyPost (returned s e r store) := by
 cases r with
 | Ok a => exact initialized a
 | Err e => trivial

def initial {H : Type} (input : Input H) : State H := {input:=input,locals:={},next:=.rounds}

theorem initial_ready {H : Type} (input : Input H) : Ready (initial input) := by
 simp [Ready,initial,rank]
#print axioms ready_returned
#print axioms initial_ready
end AspisR1.NLC_Finish
end
'''
(E/'NLC_generated/NLC_ReadyBase.lean').write_text(text)
for idx in range(4):
 text='\n'.join('import '+x['module'] for x in rows[idx*8:(idx+1)*8])+'''
import NLC_ReadyBase
import NLC_FrameAlgebra
set_option autoImplicit false
noncomputable section
namespace AspisR1.NLC_Finish
open Aeneas Aeneas.Std Result AspisR1PublicPreparation
'''
 for x in rows[idx*8:(idx+1)*8]:
  name=x['site'];text+='''
/-- Preservation of initialized slots for every possible source reply. -/
theorem ready_NAME {H : Type} (s : State H) (atSite : s.next = .NAME) (before : Ready s) :
 AllLeaves ReadyPost (step s) := by
 rw [step_NAME s atSite]
 unfold window_NAME
 repeat' first
 | (apply all_bind; intro)
 | (change ∀ _, _; intro)
 | (apply ready_returned; intro)
 | (change Ready _; simp_all [Ready,put,setNext,rank])
 | (change True; trivial)
 | split
#print axioms ready_NAME
'''.replace('NAME',name)
 text+='end AspisR1.NLC_Finish\nend\n';(E/'NLC_generated'/f'NLC_Ready{idx}.lean').write_text(text)
(E/'NLC_generated/NLC_Ready.lean').write_text(''.join(f'import NLC_Ready{i}\n' for i in range(4)))
print('Generated source initialization and four small preservation groups')
