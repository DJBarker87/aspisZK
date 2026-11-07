import NLQ_DispatchAlgebra
set_option autoImplicit false
noncomputable section
namespace NLQ_DispatchSource
open Aeneas Aeneas.Std Result AspisR1 NLQ_DispatchState NLQ_DispatchAlgebra
theorem fallback {A F C : Type} (children : Children A F C) (p : Hiq_DispatchSource.Key)
 (a : Slice A) (d : Slice U8) (world : F) :
 (NLQ_DispatchState.fallback children p a d world).result=
 (do let ten ← Hiq_DispatchSource.eqU8 d (Array.make 2#usize [3#u8,10#u8])
     if ten then (children.first p a d world).result else do
      let eleven ← Hiq_DispatchSource.eqU8 d (Array.make 2#usize [3#u8,11#u8])
      if eleven then (children.first p a d world).result else (children.second p a d world).result) := by
 simp only [NLQ_DispatchState.fallback,step_result,if_result,invoke]
/-- Exact emitted Result for the new FULL-state dispatch interpreter. The
same child run's post and internal event prefix remain in the interpreter. -/
theorem process {A F C : Type} (children : Children A F C) (p : Hiq_DispatchSource.Key)
 (a : Slice A) (d : Slice U8) (world : F) :
 (NLQ_DispatchState.process children p a d world).result=
 NIV_RawBoundary.process (NIV_RawBoundary.profile (asOps children world)) p a d := by
 unfold NLQ_DispatchState.process NIV_RawBoundary.process NIV_RawBoundary.profile
 simp only [step_result]
 congr 1
 funext head
 congr 1
 funext copied
 cases copied with
 | none => exact fallback children p a d world
 | some i =>
   dsimp only
   split <;> first | rfl | exact fallback children p a d world
theorem entry {A F C : Type} (children : Children A F C) (p : Hiq_DispatchSource.Key)
 (a : Slice A) (d : Slice U8) (world : F) :
 (NLQ_DispatchState.entry children p a d world).result=
 NIV_RawBoundary.entry (NIV_RawBoundary.profile (asOps children world)) p a d := by
 unfold NLQ_DispatchState.entry NIV_RawBoundary.entry NIV_RawBoundary.profile
 rw [step_result]
 congr 1
 funext admitted
 cases admitted <;> simp only [Bool.false_eq_true,ite_false,ite_true,process]
#print process
#print entry
#print axioms fallback
#print axioms process
#print axioms entry
end NLQ_DispatchSource
