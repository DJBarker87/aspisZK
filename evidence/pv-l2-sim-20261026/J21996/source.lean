import R1Z.PV_L2_F3SeedFrames
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_L2_F3SeedPrefix
open Aeneas Aeneas.Std Result AspisR1ProverStep8 R0Z.FsStatement
open R1Z.ProverCommitStepLoop (State)
open R1Z.ProverCommitOwnedDecoder R1Z.ProverCommitStreamSource
open R1Z.PV_L2_F3SeedFrames
variable {K : Type} [Field K] [Algebra (ZMod AspisCircleGroupOrder.P) K]

/-- Full prefix transport under an arbitrary retained E1 seed, including
None, failed reads and divergence. Counts/values are identical; actual seed
frames are substituted throughout the retained ordered read record.
This is the finite counter backend, not an adaptive-ROM equivalence. -/
theorem transport {n : Nat} (answers : Fin n → OracleAnswer) (domain : Slice U8)
    (seed : Bytes32) (L r : Nat) (state : State) :
    PV_L2_F3FullSource.produce (K := K) (blockHash answers) domain L r (reseed seed state) =
      ((PV_L2_F3FullSource.produce (K := K) (blockHash answers) domain L r state).1,
        (PV_L2_F3FullSource.produce (K := K) (blockHash answers) domain L r state).2.map (read seed)) := by
  fun_induction PV_L2_F3FullSource.produce (K := K) (blockHash answers) domain L r state <;>
    rw [PV_L2_F3FullSource.produce]
  all_goals try rfl
  all_goals rw [next_reseed]
  all_goals simp_all +zetaDelta [mapAfter,PV_L2_F3SeedFrames.read,← not_lt]

  rename_i L r state answer impossible
  cases hn : prover_commit_reference.next (blockHash answers) domain state <;>
    simp_all +zetaDelta [mapAfter,PV_L2_F3SeedFrames.read]

#print axioms transport
end R1Z.PV_L2_F3SeedPrefix
