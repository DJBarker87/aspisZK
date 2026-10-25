import T2Nat_ReaderBody
import T2Nat_QueryJoin
set_option autoImplicit false
noncomputable section
namespace AspisR1.T2Nat_TailJoin
open Aeneas Aeneas.Std Result AspisR1Stage2
open T2Nat_ResultEq

theorem normalized (reserved : Bool) (bytes : Slice U8) (v : transport.Variant)
    (next : U8) (finish : Usize) (checksum : Slice U8) (digest : Array U8 32#usize) :
    EqOk (T2Nat_ReaderBody.tail (T2Nat_ReaderOps.ops reserved) bytes v next finish checksum digest)
      (T2Nat_ReaderBody.tail (CheckpointBytes4Ops.ops reserved) bytes v next finish checksum digest) := by
  unfold T2Nat_ReaderBody.tail T2Nat_ReaderPrefix.normalized
  apply T2Nat_ResultEq.bind (T2Nat_ResultEq.refl _)
  intro different
  cases different with
  | true => exact T2Nat_ResultEq.refl _
  | false =>
    simp only [Bool.false_eq_true,ite_false]
    apply T2Nat_ResultEq.bind (T2Nat_ReaderOps.raw reserved _ _)
    rintro ⟨state,r1⟩
    apply T2Nat_ResultEq.bind (T2Nat_ReaderOps.raw reserved _ _)
    rintro ⟨root0,r2⟩
    apply T2Nat_ResultEq.bind (T2Nat_ReaderOps.raw reserved _ _)
    rintro ⟨root1,r3⟩
    apply T2Nat_Try.read_congr (T2Nat_ReaderOps.readE reserved _)
    intro gamma r4
    apply T2Nat_Try.read_congr (T2Nat_ReaderOps.readE reserved _)
    intro kappa r5
    apply T2Nat_Try.read_congr (T2Nat_ReaderOps.readE reserved _)
    intro alpha0 r6
    apply T2Nat_Try.read_congr (T2Nat_ReaderOps.readE reserved _)
    intro alpha1 r7
    apply T2Nat_Try.read_congr (T2Nat_ReaderOps.readK reserved _)
    intro rho r8
    exact T2Nat_QueryJoin.queries reserved bytes v next finish state root0 root1
      gamma kappa alpha0 alpha1 rho r8

/-- All successful outer returns, including decoder-error values, are
preserved in both directions on precisely this current source tail. -/
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
