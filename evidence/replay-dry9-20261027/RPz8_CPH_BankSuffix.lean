import RPz8_CPH_FixtureWrappers
set_option autoImplicit false
noncomputable section
namespace AspisR1.CPH_BankSuffix
open Aeneas Aeneas.Std Result S2Trust S2W_D189Entry S2W_D189Wrappers
open CPP_BankState

theorem credit_live {A : Type} (n1 : S2W_ExtractionBoundary.First) (n2 : S2W_ExtractionBoundary.Second)
    (copy : Heap (Nat → Record) → Nat → Payload → S2W_TrustedStd.Outcome (Nat → Record))
    (allocator : Allocator A) (id : S2W_ExtractionBoundary.Program) (bank : Bank)
    (key amount : Nat) (positive : 0 < bank.lamports key) :
    CPP_BankHistory.run n1 n2 copy allocator id bank [.credit key amount,.reap key,.rollback] =
      (⟨bank.cells,S2Trust.put bank.lamports key (bank.lamports key+amount)⟩,
       [.rollback,.rollback,.rollback]) := by
  have live : bank.lamports key+amount ≠ 0 := by omega
  simp only [CPP_BankHistory.run,CPP_BankState.apply,S2Trust.put,ite_true,if_neg live]

#print axioms credit_live
end AspisR1.CPH_BankSuffix
end
