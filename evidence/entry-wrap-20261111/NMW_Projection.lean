import NMW_Commands
set_option autoImplicit false
noncomputable section
namespace NMW_Projection
open Aeneas Aeneas.Std Result AspisR1 NMW_Outcome NMW_FullDispatch
def ops {A W E : Type} (children : Children A W E) (before : W) :
 Hiq_DispatchSource.Ops A where
 first := fun p a d => result (children.first ⟨p,a,d⟩ before)
 second := fun p a d => result (children.second ⟨p,a,d⟩ before)
 init := fun p a d => result (children.init ⟨p,a,d⟩ before)
 write := fun p a d => result (children.write ⟨p,a,d⟩ before)
 finalize := fun p a d => result (children.finalize ⟨p,a,d⟩ before)
/-- Scalar result of the COMPLETE interpreter is exactly the freshly emitted
frozen process; no assumption equates an observed child result to a model. -/
theorem process_result {A W E : Type} (children : Children A W E)
 (args : Args A) (before : W) (domain : NMW_RowSpecs.Release args.data) :
 result (process children args before) =
 NMW_Emitted.process (ops children before) args.program args.accounts args.data := by
 rw [NMW_Emitted.process_source]
 rcases domain with one | two
 · rw [process_first children args before one,Hiq_DispatchFirst.source _ _ _ _ one]
   rfl
 · rw [process_second children args before two,Hiq_DispatchSecond.source _ _ _ _ two]
   rfl

theorem entry_result {A W E : Type} (children : Children A W E)
 (args : Args A) (before : W) :
 result (entry children args before) =
 NMW_Emitted.entry (ops children before) args.program args.accounts args.data := by
 rw [NMW_FullDispatch.entry_total,NMW_Emitted.forwarding]
 cases Hiq_ReleaseRoute.route args.data <;> rfl
#print axioms process_result
#print axioms entry_result
end NMW_Projection
end
