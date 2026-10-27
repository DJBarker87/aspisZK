import Hir_ForeignBack
set_option autoImplicit false
noncomputable section
namespace AspisR1.Hir_CallBirth
open Aeneas Aeneas.Std Result Hist_Store Hist_RuntimeEntry
open S2Trust S2W_D189Entry S2W_D189Wrappers Hir_Call Hir_Schedule Hir_ProvenanceModel

theorem unchanged_or_birth {A : Type}
    (native1 : S2W_ExtractionBoundary.First) (native2 : S2W_ExtractionBoundary.Second)
    (copy : Heap (Nat → Record) → Nat → Payload → S2W_TrustedStd.Outcome (Nat → Record))
    (allocator : Allocator A) (id : S2W_ExtractionBoundary.Program) (store : Store) (call : Call A) (key : Nat) :
    (Hir_Call.native native1 native2 copy allocator id store call).1 key = store key ∨
      Birth native1 copy allocator id key
        ((Hir_Call.native native1 native2 copy allocator id store call).1 key).data ⟨store,call⟩ := by
  classical
  unfold Hir_Call.native
  cases route : Hiq_ReleaseRoute.route call.data with
  | reject => exact Or.inl rfl
  | second => exact Or.inl rfl
  | first =>
    unfold firstEffect
    cases reply : first native1 copy allocator (load store call.layout) id call.data call.state with
    | fail e => exact Or.inl rfl
    | div => exact Or.inl rfl
    | ok result => cases result with
      | Err e => exact Or.inl rfl
      | Ok value =>
        rcases value with ⟨saved,post,final⟩
        by_cases same : key = (call.layout.handles 2).1
        · right
          refine ⟨route,same.symm,saved,post,final,reply,?_⟩
          subst key
          simp only [commit,put_here]
        · left
          exact put_other store _ key _ same

#print axioms unchanged_or_birth
end AspisR1.Hir_CallBirth
end
