import RPz7_CPP_Invocation
import NMW_RouteFolds
set_option autoImplicit false
noncomputable section
namespace NNE_Dispatch
open Aeneas Aeneas.Std Result AspisR1 S2Trust S2W_D189Entry S2W_D189Wrappers Hist_Store
attribute [local instance] Classical.propDecidable
abbrev View := Store × S2X.AccountEvent

def view {A : Type} (effect : Hir_Call.Effect A) : View := (effect.1,effect.2.1)

/-- Error payloads do not enter the bank Step. This covers every outer
failure/divergence and every inner Err without equating their error values. -/
theorem first_error {A : Type} (store : Store) (call : Hir_Call.Call A)
 (error : CPP_Invocation.PE) :
 view (Hir_Call.firstEffect store call (ok (.Err error))) = (store,.rollback) := rfl

theorem first_failure {A : Type} (store : Store) (call : Hir_Call.Call A)
 (error : Error) :
 view (Hir_Call.firstEffect store call (.fail error)) = (store,.rollback) := rfl

theorem first_divergence {A : Type} (store : Store) (call : Hir_Call.Call A) :
 view (Hir_Call.firstEffect store call .div) = (store,.rollback) := rfl

variable {A : Type}
 (n1 : S2W_ExtractionBoundary.First) (n2 : S2W_ExtractionBoundary.Second)
 (copy : Heap (Nat → Record) → Nat → Payload → S2W_TrustedStd.Outcome (Nat → Record))
 (allocator : Allocator A) (id : S2W_ExtractionBoundary.Program)
 (store : Store) (input : CPP_Invocation.Invocation A)

theorem first_wrong_count (wrong : input.count ≠ 3) :
 view (Hir_Call.firstEffect store input.call
  (CPP_Invocation.first n1 copy allocator id store input)) = (store,.rollback) := by
 simp [CPP_Invocation.first,wrong,view,Hir_Call.firstEffect]

theorem second_view (route : Hiq_ReleaseRoute.route input.call.data = .second) :
 view (CPP_Invocation.native n1 n2 copy allocator id store input) = (store,.rollback) := by
 simp only [CPP_Invocation.native,route,view]

theorem rejected_view (route : Hiq_ReleaseRoute.route input.call.data = .reject) :
 view (CPP_Invocation.native n1 n2 copy allocator id store input) = (store,.rollback) := by
 simp only [CPP_Invocation.native,route,view]

/-- Full-outcome dispatcher substitution can be projected after composition.
This consumes NMW's SAME-argument full child packets; it does not replace them
with a success premise or a projected child law. -/
theorem entry_projection {Account World Event : Type}
 (native model : NMW_FullDispatch.Children Account World Event)
 (parentDomain child1Domain child2Domain : NMW_FullDispatch.Args Account → World → Prop)
 (stage1 : NMW_RowSpecs.RowSpec_344 native.first model.first child1Domain)
 (stage2 : NMW_RowSpecs.RowSpec_240 native.second model.second child2Domain)
 (caller1 : NMW_RowSpecs.CallerClause Hiq_ReleaseRoute.stage1 parentDomain child1Domain)
 (caller2 : NMW_RowSpecs.CallerClause Hiq_ReleaseRoute.asq8 parentDomain child2Domain)
 (projection : NMW_Outcome.Outcome World Event → View)
 (args : NMW_FullDispatch.Args Account) (before : World)
 (own : parentDomain args before)
 (admitted : Hiq_ReleaseRoute.stage1 args.data ∨ Hiq_ReleaseRoute.asq8 args.data) :
 projection (NMW_FullDispatch.entry native args before) =
 projection (NMW_FullDispatch.entry model args before) := by
 rcases admitted with h | h
 · rw [NMW_RouteFolds.entry_tx1 native model parentDomain child1Domain stage1 caller1 args before own h]
 · rw [NMW_RouteFolds.entry_tx2 native model parentDomain child2Domain stage2 caller2 args before own h]

#print axioms first_error
#print axioms first_failure
#print axioms first_divergence
#print axioms first_wrong_count
#print axioms second_view
#print axioms rejected_view
#print axioms entry_projection
end NNE_Dispatch
end
