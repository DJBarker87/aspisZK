import NLU_Execute
set_option autoImplicit false
noncomputable section
namespace AspisR1.NLU_Heads
open Aeneas Aeneas.Std Result AspisR1PublicPreparation NLC_Finish
open PreparedHashCode (Code)
/-- Exact source occurrence, with SAME immutable inputs and local slots.
This is a source/G step, not a native producer or child-domain premise. -/
def head_terminalGuard {H : Type} (s : NLC_Finish.State H) : Code (NLC_Finish.Post H) := do
 let i:=s.input
 let l:=s.locals
 let running ← read l.running
 let masked ← read l.masked
 let reject ← core.cmp.PartialEq.ne.trait_default aspis_core.field.QM31.Insts.CoreCmpPartialEqQM31 running masked
 if reject then pure (.inl (.Err r1_wire.Error.Terminal))
 else pure (.inr (setNext s .mark4))
theorem source_terminalGuard {H : Type} (s : NLU.State H) (atSite : s.machine.next=.terminalGuard) :
 NLU.step s=NLU.execute s (head_terminalGuard s.machine) := by
 rw [NLU.execute_step]
 have same : NLC_Finish.step s.machine=head_terminalGuard s.machine := by
  simp only [NLC_Finish.step,atSite]
  rfl
 rw [same]
#print axioms source_terminalGuard
end AspisR1.NLU_Heads
end
