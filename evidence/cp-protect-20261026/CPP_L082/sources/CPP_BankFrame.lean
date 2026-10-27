import CPP_BankState
import Hist_StepProtection
set_option autoImplicit false
noncomputable section
namespace AspisR1.CPP_BankFrame
open Aeneas Aeneas.Std Result Hist_Store Hist_RuntimeEntry
open S2Trust S2W_D189Entry S2W_D189Wrappers CPP_BankState
attribute [local instance] Classical.propDecidable

/-- Visible transaction-boundary accounts exclude dead cached images. This
is an initial bank representation predicate, not a retention/output premise. -/
def AtRest (bank : Bank) : Prop := ∀ key, bank.lamports key = 0 → (bank.cells key).data.val = []

theorem initial_positive (bank : Bank) (key : Nat) (atRest : AtRest bank)
    (marker : Initialized (bank.cells key).data) : 0 < bank.lamports key := by
  by_contra bad
  have zero : bank.lamports key = 0 := by omega
  have nonempty := marker.1
  rw [atRest key zero] at nonempty
  simp only [List.length_nil] at nonempty
  omega

/-- The verifier source excludes its own overwrite; external programs cannot
write/debit/reassign the protected account; credits cannot kill it; zero-balance
cleanup cannot select it. Failed operations retain their rollback projection. -/
theorem step_frame {A : Type} (ops : AdapterRw.Ops) (law : ops.op36 = Hist_Authority.keyEq)
    (n1 : S2W_ExtractionBoundary.First) (n2 : S2W_ExtractionBoundary.Second)
    (source : ∀ id accounts data, AdapterRw.r1_pool_adapter.owned.stage1_owned ops id accounts data = n1 id accounts data)
    (copy : Heap (Nat → Record) → Nat → Payload → S2W_TrustedStd.Outcome (Nat → Record))
    (std : S2W_TrustedStd.TrustedStd copy) (allocator : Allocator A)
    (id : S2W_ExtractionBoundary.Program) (bank : Bank) (action : Action A) (key : Nat)
    (owner : (bank.cells key).owner = id) (marker : Initialized (bank.cells key).data)
    (positive : 0 < bank.lamports key) :
    S2X.Preserves key (CPP_BankState.apply n1 n2 copy allocator id bank action).2 ∧
      (CPP_BankState.apply n1 n2 copy allocator id bank action).1.cells key = bank.cells key ∧
      bank.lamports key ≤ (CPP_BankState.apply n1 n2 copy allocator id bank action).1.lamports key := by
  cases action with
  | rollback => exact ⟨True.intro,rfl,le_rfl⟩
  | invoke input =>
    have classified := CPP_Classify.classified n1 n2 copy allocator id bank.cells (invocation bank input) ops law source std
    have frame := Hist_StepProtection.step_frame ops id bank.cells _ key _ classified owner marker
    exact ⟨frame.1,frame.2,le_rfl⟩
  | credit address amount =>
    refine ⟨True.intro,rfl,?_⟩
    change bank.lamports key ≤ S2Trust.put bank.lamports address (bank.lamports address + amount) key
    by_cases same : key = address
    · subst address; simp only [S2Trust.put,if_pos rfl]; omega
    · simp only [S2Trust.put,if_neg same]; exact le_rfl
  | foreign caller address value coins =>
    by_cases permitted : caller ≠ id ∧ (bank.cells address).owner = caller ∧
        (value.owner = caller ∨ Hir_ProvenanceModel.Zero value.data)
    · have different : key ≠ address := by
        intro same
        subst address
        exact permitted.1 (permitted.2.1.symm.trans owner)
      simp only [CPP_BankState.apply,if_pos permitted]
      exact ⟨different,Hist_Store.put_other _ _ _ _ different,by simp only [S2Trust.put,if_neg different]; exact le_rfl⟩
    · simp only [CPP_BankState.apply,if_neg permitted]
      exact ⟨True.intro,rfl,le_rfl⟩
  | reap address =>
    by_cases dead : bank.lamports address = 0
    · have different : key ≠ address := by intro same; subst address; omega
      simp only [CPP_BankState.apply,if_pos dead]
      exact ⟨different,Hist_Store.put_other _ _ _ _ different,le_rfl⟩
    · simp only [CPP_BankState.apply,if_neg dead]
      exact ⟨True.intro,rfl,le_rfl⟩

#print axioms initial_positive
#print axioms step_frame
end AspisR1.CPP_BankFrame
end
