import NFI_OuterCut
import NFF_LoggedOuterLoop
set_option autoImplicit false
noncomputable section
namespace AspisR1.NFI_OuterTrace
open Aeneas Aeneas.Std Result ControlFlow NFI_OuterCut

def pack (input : Input) : Result (Array U64 8#usize) → Result Returned
  | ok limbs => ok ⟨input,limbs⟩
  | fail e => fail e
  | div => div

/-- Native iteration cuts in execution order, including the cut that rejects
or diverges. Products are supplied by the inherited per-site semantic law. -/
def run (oracle : NFF_LoggedEight.Oracle) : Nat → Cut → Result Returned × List Cut
  | 0,before => (ok ⟨before.input,before.limbs⟩,[before])
  | fuel+1,before =>
    match step oracle before with
    | fail e => (fail e,[before])
    | div => (div,[before])
    | ok (done out) => (ok out,[before])
    | ok (cont after) =>
      let rest := run oracle fuel after
      (rest.1,before::rest.2)

theorem replay (oracle : NFF_LoggedEight.Oracle) (fuel : Nat) (before : Cut) :
    (run oracle fuel before).1=pack before.input
      (NFF_LoggedOuterLoop.run oracle before.input.q before.input.g before.input.slot
        fuel before.iter before.limbs) := by
  induction fuel generalizing before with
  | zero => rfl
  | succ fuel ih =>
    cases h : NFF_LoggedOuterStep.step oracle before.input.q before.input.g
        before.input.slot before.iter before.limbs with
    | fail e => simp [run,step,h,NFF_LoggedOuterLoop.run,pack]
    | div => simp [run,step,h,NFF_LoggedOuterLoop.run,pack]
    | ok out =>
      cases out with
      | done limbs => simp [run,step,h,NFF_LoggedOuterLoop.run,pack]
      | cont next =>
        rcases next with ⟨iter,limbs⟩
        simpa [run,step,h,NFF_LoggedOuterLoop.run] using
          ih (⟨before.input,iter,limbs⟩ : Cut)

theorem frames (oracle : NFF_LoggedEight.Oracle) (fuel : Nat) (before : Cut) :
    ∀ visited ∈ (run oracle fuel before).2, visited.input=before.input := by
  induction fuel generalizing before with
  | zero => intro visited hv; simp only [run,List.mem_singleton] at hv; subst visited; rfl
  | succ fuel ih =>
    cases h : step oracle before with
    | fail e => intro visited hv; simp only [run,h,List.mem_singleton] at hv; subst visited; rfl
    | div => intro visited hv; simp only [run,h,List.mem_singleton] at hv; subst visited; rfl
    | ok out =>
      cases out with
      | done after => intro visited hv; simp only [run,h,List.mem_singleton] at hv; subst visited; rfl
      | cont after =>
        intro visited hv
        simp only [run,h,List.mem_cons] at hv
        rcases hv with same | later
        · subst visited; rfl
        · exact (ih after visited later).trans (NFI_OuterCut.same_input oracle before (cont after) h)

#print axioms replay
#print axioms frames
end AspisR1.NFI_OuterTrace
end
