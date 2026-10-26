import RPz7_CPS_EntryFlags
import RPz7_CPP_BankSourceLoad
set_option autoImplicit false
noncomputable section
namespace AspisR1.CPS_BoundaryLoad
open Aeneas Aeneas.Std Result Hist_Store Hist_RuntimeEntry
open S2Trust S2W_D189Entry S2W_D189Wrappers CPP_BankState

def account (bank : Bank) (layout : Layout) (cell : Nat) : CPP_BankCache.Account :=
  ⟨(load bank.cells (CPP_BankState.layout bank layout)).records cell,(bank.cells cell).data⟩

/-- Transaction-boundary cache loading, unlike an in-transaction CPI load:
zero-funded accounts have no loaded data. The physical executor association
is not asserted by this local projection. -/
def entry (bank : Bank) (layout : Layout) : Entry :=
  { load bank.cells (CPP_BankState.layout bank layout) with
    buffers := fun cell => CPP_BankCache.image (account bank layout cell) }

theorem balance (bank : Bank) (layout : Layout) (cell : Nat) :
    (account bank layout cell).record.lamports = bank.lamports cell := rfl

theorem zero_data (bank : Bank) (layout : Layout) (cell : Nat)
    (zero : bank.lamports cell = 0) : ((entry bank layout).buffers cell).val = [] :=
  CPP_BankCache.dead_image (account bank layout cell) zero

theorem live (bank : Bank) (layout : Layout) (cell : Nat)
    (positive : 0 < bank.lamports cell) :
    (entry bank layout).buffers cell = (bank.cells cell).data := by
  change CPP_BankCache.image (account bank layout cell) = _
  unfold CPP_BankCache.image
  rw [CPP_BankCache.live _ positive]
  rfl

theorem writer_positive {A : Type} (ops : AdapterRw.Ops)
    (n1 : S2W_ExtractionBoundary.First) (n2 : S2W_ExtractionBoundary.Second)
    (hashv : S2Z.Oracle.Parts → Result S2Z.Oracle.Digest)
    (extraction : S2W_DigestExtraction.AeneasExtraction ops n1 n2 hashv)
    (copy : Heap (Nat → Record) → Nat → Payload → S2W_TrustedStd.Outcome (Nat → Record))
    (std : S2W_TrustedStd.TrustedStd copy) (allocator : Allocator A)
    (bank : Bank) (layout : Layout) (id : S2W_ExtractionBoundary.Program) (data : Slice U8)
    (state final : A) (saved : alloc.vec.Vec U8) (post : Heap (Nat → Record))
    (accepted : first n1 copy allocator (entry bank layout) id data state = ok (.Ok (saved,post,final))) :
    0 < bank.lamports (layout.handles 2).1 := by
  have native := (first_accepted n1 copy std allocator (entry bank layout) id data state final saved post accepted).1
  have source := (extraction.stage1 id (entry bank layout).first data).symm.trans native
  exact CPP_BankSourceLoad.writer_live ops (entry bank layout) id data saved
    (account bank layout (layout.handles 2).1) source rfl

#print axioms balance
#print axioms zero_data
#print axioms live
#print axioms writer_positive
end AspisR1.CPS_BoundaryLoad
end
