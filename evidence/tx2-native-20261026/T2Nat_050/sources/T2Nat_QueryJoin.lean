import T2Nat_QuerySource
import T2Nat_SuffixJoin
set_option autoImplicit false
noncomputable section
namespace AspisR1.T2Nat_QueryJoin
open Aeneas Aeneas.Std Result AspisR1Stage2
open T2Nat_ResultEq

theorem afterQueries (reserved : Bool) (bytes : Slice U8) (v : transport.Variant)
    (next : U8) (finish : Usize) (state root0 root1 : Array U8 32#usize)
    (gamma kappa alpha0 alpha1 : T2Nat_ReaderSuffix.E) (rho : T2Nat_ReaderSuffix.K)
    (queries : Array U32 22#usize) (r : verifier.Reader) :
    EqOk (T2Nat_AfterQueries.normalized (T2Nat_ReaderOps.ops reserved) bytes v next finish
      state root0 root1 gamma kappa alpha0 alpha1 rho queries r)
      (T2Nat_AfterQueries.normalized (CheckpointBytes4Ops.ops reserved) bytes v next finish
        state root0 root1 gamma kappa alpha0 alpha1 rho queries r) := by
  unfold T2Nat_AfterQueries.normalized
  rw [T2Nat_ReaderOps.validate]
  apply T2Nat_Try.ok_congr (T2Nat_ResultEq.refl _)
  intro unit
  apply T2Nat_Try.ok_congr (T2Nat_ReaderOps.semantic reserved bytes r.at)
  rintro ⟨semantic,last⟩
  exact T2Nat_SuffixJoin.normalized reserved bytes v next finish state root0 root1
    gamma kappa alpha0 alpha1 rho queries semantic {r with «at» := last}

theorem queries (reserved : Bool) (bytes : Slice U8) (v : transport.Variant)
    (next : U8) (finish : Usize) (state root0 root1 : Array U8 32#usize)
    (gamma kappa alpha0 alpha1 : T2Nat_ReaderSuffix.E) (rho : T2Nat_ReaderSuffix.K)
    (r : verifier.Reader) :
    EqOk (T2Nat_QuerySource.normalized (T2Nat_ReaderOps.ops reserved) bytes v next finish
      state root0 root1 gamma kappa alpha0 alpha1 rho r)
      (T2Nat_QuerySource.normalized (CheckpointBytes4Ops.ops reserved) bytes v next finish
        state root0 root1 gamma kappa alpha0 alpha1 rho r) := by
  unfold T2Nat_QuerySource.normalized
  apply T2Nat_ResultEq.bind (T2Nat_QueryReads.congr _ _ (T2Nat_ReaderOps.raw reserved) r)
  rintro ⟨queries,out⟩
  exact afterQueries reserved bytes v next finish state root0 root1 gamma kappa alpha0 alpha1 rho queries out

#print axioms afterQueries
#print axioms queries
end AspisR1.T2Nat_QueryJoin
end
