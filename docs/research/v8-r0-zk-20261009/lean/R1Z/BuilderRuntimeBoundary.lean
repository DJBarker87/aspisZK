import R1Z.BuilderRuntimeJoin

/-! An exact source-join obstruction at the inherited arbitrary-prover
signature. This does not assert a failure of the shipped compiler. -/
set_option autoImplicit false
noncomputable section
namespace R1Z.BuilderRuntimeBoundary
open R0P R0Z.ZkStatement R0Z.WriterRefine
variable {K : Type} [Field K] [Fintype K] [DecidableEq K]
  [Algebra (ZMod AspisCircleGroupOrder.P) K] [CharP K 2147483647]

theorem zero_padding {source : HonestProver K}
    (join : BuilderRuntimeJoin.RustRuntimeJoin source) (w : source.Instance)
    (c : Fin 29) (r : Fin 1024) (hc : 16 ≤ c.val) : source.build w c r = 0 := by
  rw [join.raw_trace_eq]
  unfold BuilderRefinement.mergedTrace copyCellMerged
  rw [if_neg (by omega)]
  unfold liftU
  simp

def mismatchProver (pub : Public K) : HonestProver K where
  Instance := Unit
  transport := BuilderSource.π
  «public» := fun _ => pub
  build := fun _ _ _ => 1

theorem no_mismatch_runtime_join (pub : Public K) :
    ¬ Nonempty (BuilderRuntimeJoin.RustRuntimeJoin (mismatchProver pub)) := by
  rintro ⟨join⟩
  have hz := zero_padding join () 16 0 (by decide)
  exact one_ne_zero (show (1 : K) = 0 from hz)

#print axioms zero_padding
#print axioms no_mismatch_runtime_join
end R1Z.BuilderRuntimeBoundary
