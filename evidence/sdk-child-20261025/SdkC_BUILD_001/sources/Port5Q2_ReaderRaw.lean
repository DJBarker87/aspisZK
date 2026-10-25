import Port4A_ReaderInstall
set_option autoImplicit false
noncomputable section
namespace AspisR1.Port5Q2_ReaderRaw
open Aeneas Aeneas.Std Result AspisR1Stage2
def raw
  (N : Std.Usize)
  (unwrap : core.result.Result (Array U8 N) core.array.TryFromSliceError → Result (Array U8 N))
  (self : verifier.Reader) :
  Result ((Array Std.U8 N) × verifier.Reader)
  := do
  let i ← lift (Std.Usize.wrapping_add self.«at» N)
  let s ←
    core.slice.index.Slice.index (core.slice.index.SliceIndexRangeUsizeSlice
      Std.U8) self.bytes { start := self.«at», «end» := i }
  let r ← core.array.TryFromArrayCopySlice.try_from N core.marker.CopyU8 s
  let b ← unwrap r
  let i1 ← lift (Std.Usize.wrapping_add self.«at» N)
  ok (b, { self with «at» := i1 })


/-- Local checked/wrapping transport, including all range/conversion failures.
Only addition is guarded; no reader success/output equality is assumed. -/
theorem normalization (N : Usize)
    (unwrap : core.result.Result (Array U8 N) core.array.TryFromSliceError → Result (Array U8 N))
    (r : verifier.Reader) (small : r.at.val+N.val≤4096) :
    raw N unwrap r=verifier.Reader.rawWithUnwrap N unwrap r := by
  unfold raw verifier.Reader.rawWithUnwrap
  rw [Port3_Wrapping.checked_add _ _ small]
  rfl

/-- Actual bounded raw read never reaches the debug-bearing panic handler.
Every possible handler gives the SAME retained reader bytes and cursor. -/
theorem reference (N : Usize)
    (unwrap : core.result.Result (Array U8 N) core.array.TryFromSliceError → Result (Array U8 N))
    (unwrap_ok : ∀ b, unwrap (.Ok b)=ok b)
    (r : verifier.Reader) (bound : r.at.val+N.val≤r.bytes.val.length)
    (size : r.bytes.val.length≤4096) :
    raw N unwrap r=CheckpointBytes3Reader.raw N r := by
  rw [normalization N unwrap r (by omega)]
  obtain ⟨b,out,run,bytes,cursor,backing⟩ := OraclePortCkptAbiReader.raw_total_exact r N unwrap unwrap_ok bound
  obtain ⟨b1,out1,run1,bytes1,cursor1,backing1⟩ :=
    OraclePortCkptAbi2Unwrap.raw_panic_unreachable r N (fun _ => fail .panic) bound
  have hb : b=b1 := Subtype.ext (bytes.trans bytes1.symm)
  have ho : out=out1 := by
    cases out with
    | mk outBytes at1 =>
      cases out1 with
      | mk outBytes1 at2 =>
        simp only [verifier.Reader.mk.injEq]
        exact ⟨backing.trans backing1.symm,UScalar.eq_of_val_eq (cursor.trans cursor1.symm)⟩
  change _=verifier.Reader.rawWithUnwrap N _ r
  rw [run,run1,hb,ho]

#print axioms normalization
#print axioms reference
end AspisR1.Port5Q2_ReaderRaw
end
