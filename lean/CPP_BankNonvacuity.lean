import CPP_BankBinding
set_option autoImplicit false
noncomputable section
namespace AspisR1.CPP_BankNonvacuity
open Aeneas Aeneas.Std Result Hist_Store Hist_RuntimeEntry
open S2Trust S2W_D189Entry S2W_D189Wrappers CPP_BankState
open Hist_Nonvacuity (key different original changed)
attribute [local instance] Classical.propDecidable

def initial : Bank := ⟨original,fun _ => 1⟩
def actions : List (Action Unit) :=
  [.credit 0 5,.foreign (key 1#u8) 1 changed 0,.reap 1,.reap 0]

theorem reached (n1 : S2W_ExtractionBoundary.First) (n2 : S2W_ExtractionBoundary.Second)
    (copy : Heap (Nat → Record) → Nat → Payload → S2W_TrustedStd.Outcome (Nat → Record))
    (allocator : Allocator Unit) :
    (CPP_BankHistory.run n1 n2 copy allocator (key 0#u8) initial actions).1.cells 0 = original 0 ∧
      (CPP_BankHistory.run n1 n2 copy allocator (key 0#u8) initial actions).1.lamports 0 = 6 ∧
      (CPP_BankHistory.run n1 n2 copy allocator (key 0#u8) initial actions).2 =
        [.rollback,.committedWrite 1 (MultiproofConeCanonical.bytesOf changed.data.val),.committedWrite 1 [],.rollback] := by
  have permitted : key 1#u8 ≠ key 0#u8 ∧ (original 1).owner = key 1#u8 ∧
      (changed.owner = key 1#u8 ∨ Hir_ProvenanceModel.Zero changed.data) := ⟨different,by simp [original],Or.inl rfl⟩
  simp [initial,actions,CPP_BankHistory.run,CPP_BankState.apply,permitted,S2Trust.put,
    Hist_Store.put,original,changed,absent]

theorem at_rest : CPP_BankFrame.AtRest initial := by
  intro key zero
  cases zero

#print axioms reached
#print axioms at_rest
end AspisR1.CPP_BankNonvacuity
end
