import T2Nat_TailFactor
set_option autoImplicit false
noncomputable section
namespace AspisR1.T2Nat_TailJoin
open Aeneas Aeneas.Std Result AspisR1Stage2
open T2Nat_ResultEq

theorem normalized (reserved : Bool) (bytes : Slice U8) (v : transport.Variant)
    (next : U8) (finish : Usize) (checksum : Slice U8) (digest : Array U8 32#usize) :
    EqOk (T2Nat_ReaderBody.tail (T2Nat_ReaderOps.ops reserved) bytes v next finish checksum digest)
      (T2Nat_ReaderBody.tail (CheckpointBytes4Ops.ops reserved) bytes v next finish checksum digest) := by
  rw [← T2Nat_TailFactor.source_eq,← T2Nat_TailFactor.source_eq]
  exact T2Nat_TailFactor.congr reserved bytes v next finish checksum digest

/-- Every returned source value, including decoder-error values, is preserved
in both directions. The field/log interpretation stays at its retained P6 port. -/
theorem source (reserved : Bool) (bytes : Slice U8) (v : transport.Variant)
    (next : U8) (finish : Usize) (checksum : Slice U8) (digest : Array U8 32#usize) :
    EqOk (Port4A_NativeReader.tail (T2Nat_ReaderOps.ops reserved) bytes v next finish checksum digest)
      (Port4A_NativeReader.tail (CheckpointBytes4Ops.ops reserved) bytes v next finish checksum digest) := by
  rw [← T2Nat_ReaderBody.source,← T2Nat_ReaderBody.source]
  exact normalized reserved bytes v next finish checksum digest

#print axioms normalized
#print axioms source
end AspisR1.T2Nat_TailJoin
end
