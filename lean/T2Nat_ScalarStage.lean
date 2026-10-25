import T2Nat_QueryJoin
set_option autoImplicit false
noncomputable section
namespace AspisR1.T2Nat_ScalarStage
open Aeneas Aeneas.Std Result AspisR1Stage2
open T2Nat_Try T2Nat_ResultEq

def body (ops : ResumeOps) (bytes : Slice U8) (v : transport.Variant)
    (next : U8) (finish : Usize) (state root0 root1 : Array U8 32#usize)
    (r : verifier.Reader) :
    Result (core.result.Result (verifier.Prepared × verifier.Accumulator) verifier.Error) :=
    withRead (ops.readE r) fun gamma r4 =>
    withRead (ops.readE r4) fun kappa r5 =>
    withRead (ops.readE r5) fun alpha0 r6 =>
    withRead (ops.readE r6) fun alpha1 r7 =>
    withRead (ops.readK r7) fun rho r8 =>
    T2Nat_QuerySource.normalized ops bytes v next finish state root0 root1 gamma kappa alpha0 alpha1 rho r8

theorem congr (reserved : Bool) (bytes : Slice U8) (v : transport.Variant)
    (next : U8) (finish : Usize) (state root0 root1 : Array U8 32#usize) (r : verifier.Reader) :
    EqOk (body (T2Nat_ReaderOps.ops reserved) bytes v next finish state root0 root1 r)
      (body (CheckpointBytes4Ops.ops reserved) bytes v next finish state root0 root1 r) := by
  unfold body
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
  exact T2Nat_QueryJoin.queries reserved bytes v next finish state root0 root1 gamma kappa alpha0 alpha1 rho r8

#print axioms congr
end AspisR1.T2Nat_ScalarStage
end
