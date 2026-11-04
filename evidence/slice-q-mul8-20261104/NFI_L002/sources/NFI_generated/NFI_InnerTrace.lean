import NFI_InnerCut
import NFF_LoggedLoop
set_option autoImplicit false
noncomputable section
namespace AspisR1.NFI_InnerTrace
open Aeneas Aeneas.Std Result ControlFlow NFI_InnerCut

def pack (input : Input) : Result (Array U64 8#usize) → Result Returned
  | ok sums => ok ⟨input,sums⟩
  | fail e => fail e
  | div => div

/-- Native iteration cuts in execution order, including the cut that rejects
or diverges. Products are supplied by the inherited per-site semantic law. -/
def run (oracle : NFF_LoggedEight.Oracle) : Nat → Cut → Result Returned × List Cut
  | 0,before => (ok ⟨before.input,before.sums⟩,[before])
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
      (NFF_LoggedLoop.run oracle before.input.q before.input.g before.input.slot
        fuel before.iter before.sums) := by
  induction fuel generalizing before with
  | zero => rfl
  | succ fuel ih =>
    cases h : NFF_LoggedStep.step oracle before.input.q before.input.g
        before.input.slot before.iter before.sums with
    | fail e => simp [run,step,h,NFF_LoggedLoop.run,pack]
    | div => simp [run,step,h,NFF_LoggedLoop.run,pack]
    | ok out =>
      cases out with
      | done sums => simp [run,step,h,NFF_LoggedLoop.run,pack]
      | cont next =>
        rcases next with ⟨iter,sums⟩
        simpa [run,step,h,NFF_LoggedLoop.run] using
          ih (⟨before.input,iter,sums⟩ : Cut)

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
        · exact (ih after visited later).trans (NFI_InnerCut.same_input oracle before (cont after) h)

#print axioms replay
#print axioms frames
end AspisR1.NFI_InnerTrace
end
