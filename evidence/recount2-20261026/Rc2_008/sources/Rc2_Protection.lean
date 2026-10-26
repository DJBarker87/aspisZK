import CPR_AtomicBank
set_option autoImplicit false
noncomputable section
namespace AspisR1.Rc2_Protection
open Aeneas Aeneas.Std Result S2Trust S2W_D189Entry S2W_D189Wrappers S2W_TrustedStd
open CPP_BankState

def Facts {A F C : Type} (c : DrvC_Installation.Configuration F C)
    (n1 : S2W_ExtractionBoundary.First) (n2 : S2W_ExtractionBoundary.Second)
    (copy : Heap (Nat → Record) → Nat → Payload → Outcome (Nat → Record))
    (allocator : Allocator A) (id : S2W_ExtractionBoundary.Program) : Prop :=
  ∀ (keyLaw : (DrvC_Installation.sdk c).op36 = Hist_Authority.keyEq)
    (before : Bank) (actions : List (Action A)) (success : Bool),
    byteLedger (CPR_AtomicBank.run n1 n2 copy allocator id before actions success).1.cells =
      S2X.history (byteLedger before.cells)
        (CPR_AtomicBank.run n1 n2 copy allocator id before actions success).2 ∧
    ∀ (key : Nat) (owner : (before.cells key).owner = id)
      (marker : Hist_RuntimeEntry.Initialized (before.cells key).data)
      (positive : 0 < before.lamports key),
      (∀ event ∈ (CPR_AtomicBank.run n1 n2 copy allocator id before actions success).2,
        S2X.Preserves key event) ∧
      (CPR_AtomicBank.run n1 n2 copy allocator id before actions success).1.cells key = before.cells key ∧
      before.lamports key ≤ (CPR_AtomicBank.run n1 n2 copy allocator id before actions success).1.lamports key

theorem derive {A F C : Type} (c : DrvC_Installation.Configuration F C)
    (hashv : S2Z.Oracle.Parts → Result S2Z.Oracle.Digest)
    (n1 : S2W_ExtractionBoundary.First) (n2 : S2W_ExtractionBoundary.Second)
    (extraction : S2W_DigestExtraction.AeneasExtraction (DrvC_Installation.sdk c) n1 n2 hashv)
    (copy : Heap (Nat → Record) → Nat → Payload → Outcome (Nat → Record))
    (std : TrustedStd copy) (allocator : Allocator A) (id : S2W_ExtractionBoundary.Program) :
    Facts c n1 n2 copy allocator id := by
  intro keyLaw before actions success
  have source := fun id accounts data => (extraction.stage1 id accounts data).symm
  exact ⟨CPR_AtomicBank.effect (DrvC_Installation.sdk c) keyLaw n1 n2 source copy std allocator id before actions success,
    CPR_AtomicBank.protection (DrvC_Installation.sdk c) keyLaw n1 n2 source copy std allocator id before actions success⟩
#print axioms derive
end AspisR1.Rc2_Protection
end
