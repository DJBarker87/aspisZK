import NNE_Observed
import NNE_AbortRollback
import NNE_RslError
set_option autoImplicit false
noncomputable section
namespace NNE_RollbackView
open Aeneas Aeneas.Std Result AspisR1 S2Trust S2W_D189Entry S2W_D189Wrappers
open Hist_Store Hist_RuntimeEntry CPP_BankState
open RSL RSL.TAS NNE_Observed

theorem lift (n1 : S2W_ExtractionBoundary.First) (n2 : S2W_ExtractionBoundary.Second)
 (copy : Heap (Nat → Record) → Nat → Payload → S2W_TrustedStd.Outcome (Nat → Record))
 (p : S2W_ExtractionBoundary.Program) (before : Bank) (input : CPP_Invocation.Invocation Bool)
 (h : NNE_Dispatch.view (CPP_Invocation.native n1 n2 copy NNE_AbortIndicator.allocator p
  before.cells (CPP_BankState.invocation before input)) = (before.cells,.rollback)) :
 CPP_BankState.apply n1 n2 copy NNE_AbortIndicator.allocator p before (.invoke input) =
 (before,.rollback) := by
 exact congrArg (fun v : NNE_Dispatch.View => (Bank.mk v.1 before.lamports,v.2)) h

theorem frame (before after : Bank) (input : CPP_Invocation.Invocation Bool)
 (o : Observation) (event : S2X.AccountEvent) (rep : Assoc before after input o event)
 (g2 : Frame (state before input) o) : after = before ∧ event = .rollback := by
 cases ho : o.exit with
 | abort => simpa [Assoc,ho] using rep.2
 | diverge => simpa [Assoc,ho] using rep.2
 | ret value =>
  rcases value with ⟨r,post⟩
  cases r with
  | error e => simpa [Assoc,ho] using rep.2
  | ok value =>
   cases value
   have hr := rep.2
   rw [ho] at hr
   exact ⟨NNE_BankImage.frame before after _ post (NNE_BankImage.loaded before _ 0)
     hr.1 hr.2.1 (g2.2 _ post ho),hr.2.2.1.1 g2.1⟩

/-- ASQ8 consumes G2 alone, including errors and aborts, at any count. -/
theorem asq8 (n1 : S2W_ExtractionBoundary.First) (n2 : S2W_ExtractionBoundary.Second)
 (copy : Heap (Nat → Record) → Nat → Payload → S2W_TrustedStd.Outcome (Nat → Record))
 (p : S2W_ExtractionBoundary.Program) (before after : Bank) (input : CPP_Invocation.Invocation Bool)
 (o : Observation) (event : S2X.AccountEvent) (rep : Assoc before after input o event)
 (g2 : Frame (state before input) o)
 (route : Hiq_ReleaseRoute.route input.call.data = .second) :
 CPP_BankState.apply n1 n2 copy NNE_AbortIndicator.allocator p before (.invoke input) =
 (after,event) := by
 obtain ⟨ha,he⟩ := frame before after input o event rep g2
 subst after; subst event
 apply lift
 exact NNE_Dispatch.second_view n1 n2 copy NNE_AbortIndicator.allocator p before.cells
   (CPP_BankState.invocation before input) route

/-- An aborted stage1 call cannot commit even when its allocation list is empty. -/
theorem aborted (n1 : S2W_ExtractionBoundary.First) (n2 : S2W_ExtractionBoundary.Second)
 (copy : Heap (Nat → Record) → Nat → Payload → S2W_TrustedStd.Outcome (Nat → Record))
 (p : S2W_ExtractionBoundary.Program) (before : Bank) (input : CPP_Invocation.Invocation Bool)
 (route : Hiq_ReleaseRoute.stage1 input.call.data) (stopped : input.call.state = false) :
 CPP_BankState.apply n1 n2 copy NNE_AbortIndicator.allocator p before (.invoke input) =
 (before,.rollback) := by
 apply lift
 have rout := (Hiq_ReleaseRoute.first_iff _).mpr route
 simp only [CPP_Invocation.native,CPP_BankState.invocation,rout]
 by_cases count : input.count = 3
 · simpa only [CPP_Invocation.first,CPP_BankState.invocation,route,count,and_self,ite_true,stopped,entry]
    using NNE_AbortRollback.first n1 copy (entry before input) p input.call.data before.cells
      (CPP_BankState.invocation before input).call
 · exact NNE_Dispatch.first_wrong_count n1 copy NNE_AbortIndicator.allocator p before.cells
     (CPP_BankState.invocation before input) count

#print axioms lift
#print axioms frame
#print axioms asq8
#print axioms aborted
end NNE_RollbackView
end
