import NLU_Next
set_option autoImplicit false
noncomputable section
namespace AspisR1.NLU
open Aeneas Aeneas.Std Result AspisR1PublicPreparation
def Invariant {H : Type} (s : NLU.State H) : Prop :=
 NLC_Finish.Ready s.machine ∧ NLC_Finish.Major s.machine ∧ Linear s
inductive Reachable {H : Type} (input : Input H) : NLU.State H → Prop where
 | initial : Reachable input (NLU.initial input)
 | next {s after : NLU.State H} (before : Reachable input s)
   (head : (step s).reply=.ok (.inr after)) : Reachable input after
theorem initial_invariant {H : Type} (i : Input H) : Invariant (initial i) := by
 refine ⟨NLC_Finish.initial_ready i,?_,initial_linear i⟩
 change 0<32
 decide
theorem next_invariant {H : Type} (s after : NLU.State H) (before : Invariant s)
 (head : (step s).reply=.ok (.inr after)) : Invariant after := by
 have actual:=(next_characterization s after head).1
 exact ⟨NLC_Finish.source_ready_next _ _ before.1 actual,
  NLC_Finish.source_major_next _ _ before.2.1 actual,next_linear s after before.2.2 head⟩
theorem reachable_invariant {H : Type} (i : Input H) (s : NLU.State H) (reached : Reachable i s) :
 Invariant s ∧ s.machine.input=i := by
 induction reached with
 | initial => exact ⟨initial_invariant i,rfl⟩
 | next before head ih => exact ⟨next_invariant _ _ ih.1 head,(next_input _ _ head).trans ih.2⟩
#print axioms initial_invariant
#print axioms next_invariant
#print axioms reachable_invariant
end AspisR1.NLU
end
