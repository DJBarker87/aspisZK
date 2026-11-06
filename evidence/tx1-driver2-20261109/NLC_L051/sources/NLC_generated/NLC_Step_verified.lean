import NLC_FinishStep
set_option autoImplicit false
noncomputable section
namespace AspisR1.NLC_Finish
open Aeneas Aeneas.Std Result AspisR1PublicPreparation
open PreparedHashCode (Code)
/-- Source dispatcher window only; no native/harness association is inferred. -/
def window_verified {H : Type} (s : State H) : Code (Post H) := do
 let i := s.input
 let l := s.locals
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
/-- Exact SAME-state source step. The native cut is not a hypothesis of this theorem. -/
theorem step_verified {H : Type} (s : State H) (atSite : s.next = .verified) :
 step s = window_verified s := by
 rcases s with ⟨i,l,next⟩
 cases atSite
 rfl
#print axioms step_verified
#print step_verified
end AspisR1.NLC_Finish
end
