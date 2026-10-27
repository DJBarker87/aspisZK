import Hist_InitialZero
import S2W_D189Wrappers
set_option autoImplicit false
noncomputable section
namespace AspisR1.Hist_NativeReject
open Aeneas Aeneas.Std Result
open S2Trust S2W_D189Entry S2W_D189Wrappers S2W_TrustedStd

/-- Lift the source zero-gate obstruction to the same native wrapper boundary
already consumed by the accepted-pair theorem. No new source port is added. -/
theorem no_reinitialize {A : Type}
    (ops : AdapterRw.Ops) (native1 : S2W_ExtractionBoundary.First)
    (native2 : S2W_ExtractionBoundary.Second)
    (hashv : S2Z.Oracle.Parts → Result S2Z.Oracle.Digest)
    (extraction : S2W_DigestExtraction.AeneasExtraction ops native1 native2 hashv)
    (copy : Heap (Nat → Record) → Nat → Payload → Outcome (Nat → Record))
    (std : TrustedStd copy) (allocator : Allocator A) (e : Entry)
    (program : S2W_ExtractionBoundary.Program) (data : Slice U8) (state final : A)
    (saved : alloc.vec.Vec U8) (post : Heap (Nat → Record))
    (head : U8) (nonempty : 0 < (e.buffers (e.handles 2).1).val.length)
    (read : Slice.index_usize (e.buffers (e.handles 2).1) 0#usize = ok head)
    (nonzero : head ≠ 0#u8) :
    first native1 copy allocator e program data state ≠ ok (.Ok (saved,post,final)) := by
  intro accepted
  have native := (first_accepted native1 copy std allocator e program data state final saved post accepted).1
  rw [extraction.stage1] at native
  exact Hist_InitialZero.no_reinitialize e ops program data saved head nonempty read nonzero native

#print axioms no_reinitialize
end AspisR1.Hist_NativeReject
end
