import R1Z.PV_L2_Premises
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_L2_PremisesBound
open R0Z R0Z.FsStatement R0Z.FsAbort R0Z.FsGood R0Z.HvzkV
open R1Z.ProverCommitFuelJoin22 R1Z.PV_L2_Premises
variable {R M V Proof Obs : Type} [Fintype R] [Fintype M] [Nonempty M]
variable {runtime : R → V} {model : M → V}
variable {old : Fin 8 → M → Prop}
variable {queries : M → List ProverCommitSeedEvent19.Entry}

/-- All row observations together incur the ORIGINAL charge once, not once
per row. This remains conditional on every explicitly named row field. It
is real-to-source, and is not source-to-simE absorption of the full record. -/
theorem joint_test_bound (join : RunJoin runtime model old queries)
    (realRun : R → PV_L2_F3FullRetry.Run Proof)
    (modelRun : M → PV_L2_F3FullRetry.Run Proof)
    (realRows : R → Row → Obs) (modelRows : M → Row → Obs)
    (p : PV_L2_Premises join realRun modelRun realRows modelRows)
    (test : V × PV_L2_F3FullRetry.Run Proof × (Row → Obs) → ℚ)
    (bounded : ∀ value, 0≤test value ∧ test value≤1)
    (q : Nat) (bound : ∀ m, (queries m).length≤q) :
    |mean (fun r => test (runtime r,realRun r,realRows r)) -
      mean (fun m => test (model m,modelRun m,modelRows m))| ≤
      eventMass (fun m => ∃ i, old i m) + ProverCommitSeedEvent19.budget q +
        ProverCommitFuelMass22.charge :=
  ProverCommitFuelJoin22.test_bound
    (PV_L2_Premises.extend join realRun modelRun realRows modelRows p) test bounded q bound

#print axioms joint_test_bound
end R1Z.PV_L2_PremisesBound
