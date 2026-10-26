import CPP_BankCache
set_option autoImplicit false
noncomputable section
namespace AspisR1.CPP_BankCacheGap
open Aeneas Aeneas.Std Result S2W_D189Entry Hist_Store CPP_BankCache

/-- A representation countermodel: owner/data/marker alone do not supply a
bank load. This is not an accepted native/runtime cryptographic fixture. -/
theorem marker_but_absent (record : Record) :
    ∃ account : Account, Initialized account.data ∧ account.record.lamports = 0 ∧ load account = none := by
  exact ⟨⟨{record with lamports := 0},Hist_Nonvacuity.checkpoint⟩,Hist_Nonvacuity.initialized,rfl,rfl⟩

theorem marker_not_sufficient (record : Record) :
    ¬ (∀ account : Account, Initialized account.data → ∃ value, load account = some value) := by
  intro sufficient
  obtain ⟨account,marker,zero,absent⟩ := marker_but_absent record
  obtain ⟨value,loaded⟩ := sufficient account marker
  rw [absent] at loaded
  cases loaded

#print axioms marker_but_absent
#print axioms marker_not_sufficient
end AspisR1.CPP_BankCacheGap
end
