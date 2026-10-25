import T2Nat_ReaderSuffix
import T2Nat_ReaderOps
set_option autoImplicit false
noncomputable section
namespace AspisR1.T2Nat_SuffixJoin
open Aeneas Aeneas.Std Result AspisR1Stage2
open T2Nat_Try T2Nat_ResultEq T2Nat_ReaderSuffix

theorem normalized (reserved : Bool) (bytes : Slice U8) (v : transport.Variant)
    (next : U8) (finish : Usize) (state root0 root1 : Array U8 32#usize)
    (gamma kappa alpha0 alpha1 : E) (rho : K) (queries : Array U32 22#usize)
    (semantic : Array K 10#usize) (r : verifier.Reader) :
    EqOk (T2Nat_ReaderSuffix.normalized (T2Nat_ReaderOps.ops reserved) bytes v next finish
      state root0 root1 gamma kappa alpha0 alpha1 rho queries semantic r)
      (T2Nat_ReaderSuffix.normalized (CheckpointBytes4Ops.ops reserved) bytes v next finish
        state root0 root1 gamma kappa alpha0 alpha1 rho queries semantic r) := by
  unfold T2Nat_ReaderSuffix.normalized
  apply T2Nat_Try.read_congr (T2Nat_ReaderOps.readK reserved _)
  intro zx0 r0
  apply T2Nat_Try.read_congr (T2Nat_ReaderOps.readK reserved _)
  intro zy0 r1
  apply T2Nat_Try.read_congr (T2Nat_ReaderOps.readK reserved _)
  intro zx1 r2
  apply T2Nat_Try.read_congr (T2Nat_ReaderOps.readK reserved _)
  intro zy1 r3
  apply T2Nat_Try.read_congr (T2Nat_ReaderOps.readE reserved _)
  intro claim r4
  apply T2Nat_Try.read_congr (T2Nat_ReaderOps.readE reserved _)
  intro rhs r5
  apply T2Nat_Try.read_congr (T2Nat_ReaderOps.readK reserved _)
  intro power r6
  apply T2Nat_ResultEq.bind (T2Nat_ResultEq.refl _)
  intro width
  apply T2Nat_ResultEq.bind (T2Nat_ResultEq.refl _)
  intro zero
  apply T2Nat_Try.ok_congr (T2Nat_ResultEq.refl _)
  intro initial
  apply T2Nat_Try.ok_congr (T2Nat_ReaderOps.weights reserved bytes r6.at initial)
  rintro ⟨weights,last⟩
  exact T2Nat_ResultEq.refl _

#print axioms normalized
end AspisR1.T2Nat_SuffixJoin
end
