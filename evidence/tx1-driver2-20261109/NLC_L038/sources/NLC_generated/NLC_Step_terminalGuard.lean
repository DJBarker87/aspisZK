import NLC_FinishStep
set_option autoImplicit false
noncomputable section
namespace AspisR1.NLC_Finish
open Aeneas Aeneas.Std Result AspisR1PublicPreparation
open PreparedHashCode (Code)
/-- Source dispatcher window only; no native/harness association is inferred. -/
def window_terminalGuard {H : Type} (s : State H) : Code (Post H) := do
 let i := s.input
 let l := s.locals
 let running ← read l.running
 let masked ← read l.masked
 let reject ← core.cmp.PartialEq.ne.trait_default aspis_core.field.QM31.Insts.CoreCmpPartialEqQM31 running masked
 if reject then pure (.inl (.Err r1_wire.Error.Terminal))
 else pure (.inr (setNext s .mark4))
/-- Exact SAME-state source step. The native cut is not a hypothesis of this theorem. -/
theorem step_terminalGuard {H : Type} (s : State H) (atSite : s.next = .terminalGuard) :
 step s = window_terminalGuard s := by
 rcases s with ⟨i,l,next⟩
 cases atSite
 rfl
#print axioms step_terminalGuard
#print step_terminalGuard
end AspisR1.NLC_Finish
end
