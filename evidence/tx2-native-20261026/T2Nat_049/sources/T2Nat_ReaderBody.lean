import T2Nat_ReaderPrefix
set_option autoImplicit false
noncomputable section
namespace AspisR1.T2Nat_ReaderBody
open Aeneas Aeneas.Std Result AspisR1Stage2

abbrev tail := T2Nat_ReaderPrefix.normalized

/-- Complete current emitted tail, checked through separately normalized
prefix, query and suffix declarations. No recursion/heartbeat cap increase. -/
theorem source (ops : ResumeOps) (bytes : Slice U8) (v : transport.Variant)
    (next : U8) (finish : Usize) (checksum : Slice U8) (digest : Array U8 32#usize) :
    tail ops bytes v next finish checksum digest =
      Port4A_NativeReader.tail ops bytes v next finish checksum digest :=
  (T2Nat_ReaderPrefix.normalize ops bytes v next finish checksum digest).symm.trans
    (T2Nat_ReaderPrefix.source_eq ops bytes v next finish checksum digest)

#print axioms source
end AspisR1.T2Nat_ReaderBody
end
