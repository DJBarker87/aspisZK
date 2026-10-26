import CPP_BankFrame
set_option autoImplicit false
noncomputable section
namespace AspisR1.CPP_BankHistory
open Aeneas Aeneas.Std Result Hist_Store Hist_RuntimeEntry
open S2Trust S2W_D189Entry S2W_D189Wrappers CPP_BankState

def run {A : Type} (n1 : S2W_ExtractionBoundary.First) (n2 : S2W_ExtractionBoundary.Second)
    (copy : Heap (Nat → Record) → Nat → Payload → S2W_TrustedStd.Outcome (Nat → Record))
    (allocator : Allocator A) (id : S2W_ExtractionBoundary.Program) (bank : Bank) :
    List (Action A) → Bank × List S2X.AccountEvent
  | [] => (bank,[])
  | action :: rest =>
    let head := CPP_BankState.apply n1 n2 copy allocator id bank action
    let tail := run n1 n2 copy allocator id head.1 rest
    (tail.1,head.2 :: tail.2)

theorem protection {A : Type} (ops : AdapterRw.Ops) (law : ops.op36 = Hist_Authority.keyEq)
    (n1 : S2W_ExtractionBoundary.First) (n2 : S2W_ExtractionBoundary.Second)
    (source : ∀ id accounts data, AdapterRw.r1_pool_adapter.owned.stage1_owned ops id accounts data = n1 id accounts data)
    (copy : Heap (Nat → Record) → Nat → Payload → S2W_TrustedStd.Outcome (Nat → Record))
    (std : S2W_TrustedStd.TrustedStd copy) (allocator : Allocator A)
    (id : S2W_ExtractionBoundary.Program) (bank : Bank) (actions : List (Action A)) (key : Nat)
    (owner : (bank.cells key).owner = id) (marker : Initialized (bank.cells key).data)
    (positive : 0 < bank.lamports key) :
    (∀ event ∈ (run n1 n2 copy allocator id bank actions).2, S2X.Preserves key event) ∧
      (run n1 n2 copy allocator id bank actions).1.cells key = bank.cells key ∧
      bank.lamports key ≤ (run n1 n2 copy allocator id bank actions).1.lamports key := by
  induction actions generalizing bank with
  | nil => exact ⟨by simp [run],rfl,le_rfl⟩
  | cons action rest ih =>
    let head := CPP_BankState.apply n1 n2 copy allocator id bank action
    obtain ⟨headPreserves,headCell,headBalance⟩ :=
      CPP_BankFrame.step_frame ops law n1 n2 source copy std allocator id bank action key owner marker positive
    obtain ⟨tailPreserves,tailCell,tailBalance⟩ := ih head.1
      (by rw [headCell]; exact owner) (by rw [headCell]; exact marker) (lt_of_lt_of_le positive headBalance)
    refine ⟨?_,tailCell.trans headCell,headBalance.trans tailBalance⟩
    intro event member
    rcases List.mem_cons.mp member with same | later
    · subst event; exact headPreserves
    · exact tailPreserves event later

#print axioms protection
end AspisR1.CPP_BankHistory
end
