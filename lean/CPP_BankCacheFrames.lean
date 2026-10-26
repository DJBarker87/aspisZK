import CPP_BankCache
set_option autoImplicit false
noncomputable section
namespace AspisR1.CPP_BankCacheFrames
open Aeneas Aeneas.Std Result S2Trust S2W_D189Entry S2W_D189Wrappers

/-- A verifier's accepted copy preserves the entire account record. This
includes lamports/rent/owner/executable/key and excludes a source close or
reassign; resizing is excluded separately by the descriptor frame. -/
theorem record {A : Type} (n1 : S2W_ExtractionBoundary.First)
    (copy : Heap (Nat → Record) → Nat → Payload → S2W_TrustedStd.Outcome (Nat → Record))
    (std : S2W_TrustedStd.TrustedStd copy) (allocator : Allocator A) (e : Entry)
    (id : S2W_ExtractionBoundary.Program) (data : Slice U8) (state final : A)
    (saved : alloc.vec.Vec U8) (post : Heap (Nat → Record))
    (accepted : first n1 copy allocator e id data state = ok (.Ok (saved,post,final))) (cell : Nat) :
    post.ambient cell = e.records cell :=
  congrArg (fun records => records cell) (CPP_Metadata.first_frame n1 copy std allocator e id data state final saved post accepted).1

theorem remains_cached {A : Type} (n1 : S2W_ExtractionBoundary.First)
    (copy : Heap (Nat → Record) → Nat → Payload → S2W_TrustedStd.Outcome (Nat → Record))
    (std : S2W_TrustedStd.TrustedStd copy) (allocator : Allocator A) (e : Entry)
    (id : S2W_ExtractionBoundary.Program) (data : Slice U8) (state final : A)
    (saved : alloc.vec.Vec U8) (post : Heap (Nat → Record))
    (accepted : first n1 copy allocator e id data state = ok (.Ok (saved,post,final)))
    (wasLoaded : CPP_BankCache.load ⟨e.records (e.handles 2).1,e.buffers (e.handles 2).1⟩ =
      some ⟨e.records (e.handles 2).1,e.buffers (e.handles 2).1⟩) :
    CPP_BankCache.load ⟨post.ambient (e.handles 2).1,saved.deref⟩ =
      some ⟨post.ambient (e.handles 2).1,saved.deref⟩ := by
  have positive := (CPP_BankCache.loaded _ _ wasLoaded).2
  apply CPP_BankCache.live
  change 0 < (post.ambient (e.handles 2).1).lamports
  rw [record n1 copy std allocator e id data state final saved post accepted]
  exact positive

#print axioms record
#print axioms remains_cached
end AspisR1.CPP_BankCacheFrames
end
