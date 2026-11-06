import NLU_Execute
set_option autoImplicit false
noncomputable section
namespace AspisR1.NLU_Heads
open Aeneas Aeneas.Std Result AspisR1PublicPreparation NLC_Finish
open PreparedHashCode (Code)
/-- Exact source occurrence, with SAME immutable inputs and local slots.
This is a source/G step, not a native producer or child-domain premise. -/
def head_verified {H : Type} (s : NLC_Finish.State H) : Code (NLC_Finish.Post H) := do
 let i:=s.input
 let l:=s.locals
 let root ← read l.root
 let alpha ← read l.alpha
 let claims ← read l.claims
 let extra ← read l.extra
 let beforeZ1 ← read l.beforeZ1
 let stateBefore ← read l.stateBefore
 let z0 ← read l.z0
 let z1 ← read l.z1
 let transcript ← read l.transcript
 pure (.inl (.Ok {
   roots := (Array.make 2#usize [i.prefix1.c1_root, root]),
   challenges := i.challenges,
   alpha := alpha,
   claims := claims,
   extra := extra,
   before_z1 := beforeZ1,
   state_before_z0 := stateBefore,
   z := (Array.make 2#usize [z0,z1]),
   transcript := transcript }))
theorem source_verified {H : Type} (s : NLU.State H) (atSite : s.machine.next=.verified) :
 NLU.step s=NLU.execute s (head_verified s.machine) := by
 rw [NLU.execute_step]
 have same : NLC_Finish.step s.machine=head_verified s.machine := by
  simp only [NLC_Finish.step,atSite]
  rfl
 rw [same]
#print axioms source_verified
end AspisR1.NLU_Heads
end
