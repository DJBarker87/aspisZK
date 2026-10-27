import R1Z.PV_L2_F3FullRetry
import R1Z.ProverCommitFuelJoin22

/-! Explicit row obligations on an EXISTING headline RunJoin coupling.
This is premise accounting, not discharge of native source agreement.
In particular no independent coupling for a trace marginal is accepted. -/
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_L2_Premises
open R0Z R0Z.FsStatement R0Z.FsGood R0Z.HvzkV R0Z.HvzkS
open R1Z.ProverCommitFuelJoin22
attribute [local instance] Classical.propDecidable

inductive Row where
  | v352 | v353 | v354 | v355 | v356 | v357 | v358 | v359
  | v360 | v361 | v362 | v363 | v364 | v365 | v367 | v368 | v369 | inversion380
  deriving DecidableEq

variable {R M V Proof Obs : Type} [Fintype R] [Fintype M]
variable {runtime : R → V} {model : M → V}
variable {old : Fin 8 → M → Prop}
variable {queries : M → List ProverCommitSeedEvent19.Entry}

/-- `old` is supplied by the endpoint as its actual realBad; it is not
replaced by a newly defined trace-mismatch event. V366 retains whole runs. -/
structure PV_L2_Premises (join : RunJoin runtime model old queries)
    (realRun : R → PV_L2_F3FullRetry.Run Proof)
    (modelRun : M → PV_L2_F3FullRetry.Run Proof)
    (realRows : R → Row → Obs) (modelRows : M → Row → Obs) : Prop where
  V352 : ∀ s, ¬(∃ i, bad old queries i (join.cp.toM s)) →
    realRows (join.cp.toR s) .v352 = modelRows (join.cp.toM s).1.1 .v352
  V353 : ∀ s, ¬(∃ i, bad old queries i (join.cp.toM s)) →
    realRows (join.cp.toR s) .v353 = modelRows (join.cp.toM s).1.1 .v353
  V354 : ∀ s, ¬(∃ i, bad old queries i (join.cp.toM s)) →
    realRows (join.cp.toR s) .v354 = modelRows (join.cp.toM s).1.1 .v354
  V355 : ∀ s, ¬(∃ i, bad old queries i (join.cp.toM s)) →
    realRows (join.cp.toR s) .v355 = modelRows (join.cp.toM s).1.1 .v355
  V356 : ∀ s, ¬(∃ i, bad old queries i (join.cp.toM s)) →
    realRows (join.cp.toR s) .v356 = modelRows (join.cp.toM s).1.1 .v356
  V357 : ∀ s, ¬(∃ i, bad old queries i (join.cp.toM s)) →
    realRows (join.cp.toR s) .v357 = modelRows (join.cp.toM s).1.1 .v357
  V358 : ∀ s, ¬(∃ i, bad old queries i (join.cp.toM s)) →
    realRows (join.cp.toR s) .v358 = modelRows (join.cp.toM s).1.1 .v358
  V359 : ∀ s, ¬(∃ i, bad old queries i (join.cp.toM s)) →
    realRows (join.cp.toR s) .v359 = modelRows (join.cp.toM s).1.1 .v359
  V360 : ∀ s, ¬(∃ i, bad old queries i (join.cp.toM s)) →
    realRows (join.cp.toR s) .v360 = modelRows (join.cp.toM s).1.1 .v360
  V361 : ∀ s, ¬(∃ i, bad old queries i (join.cp.toM s)) →
    realRows (join.cp.toR s) .v361 = modelRows (join.cp.toM s).1.1 .v361
  V362 : ∀ s, ¬(∃ i, bad old queries i (join.cp.toM s)) →
    realRows (join.cp.toR s) .v362 = modelRows (join.cp.toM s).1.1 .v362
  V363 : ∀ s, ¬(∃ i, bad old queries i (join.cp.toM s)) →
    realRows (join.cp.toR s) .v363 = modelRows (join.cp.toM s).1.1 .v363
  V364 : ∀ s, ¬(∃ i, bad old queries i (join.cp.toM s)) →
    realRows (join.cp.toR s) .v364 = modelRows (join.cp.toM s).1.1 .v364
  V365 : ∀ s, ¬(∃ i, bad old queries i (join.cp.toM s)) →
    realRows (join.cp.toR s) .v365 = modelRows (join.cp.toM s).1.1 .v365
  V366 : ∀ s, ¬(∃ i, bad old queries i (join.cp.toM s)) →
    realRun (join.cp.toR s) = modelRun (join.cp.toM s).1.1
  V367 : ∀ s, ¬(∃ i, bad old queries i (join.cp.toM s)) →
    realRows (join.cp.toR s) .v367 = modelRows (join.cp.toM s).1.1 .v367
  V368 : ∀ s, ¬(∃ i, bad old queries i (join.cp.toM s)) →
    realRows (join.cp.toR s) .v368 = modelRows (join.cp.toM s).1.1 .v368
  V369 : ∀ s, ¬(∃ i, bad old queries i (join.cp.toM s)) →
    realRows (join.cp.toR s) .v369 = modelRows (join.cp.toM s).1.1 .v369
  V380_inversion : ∀ s, ¬(∃ i, bad old queries i (join.cp.toM s)) →
    realRows (join.cp.toR s) .inversion380 = modelRows (join.cp.toM s).1.1 .inversion380

theorem rows_agree (join : RunJoin runtime model old queries)
    (realRun : R → PV_L2_F3FullRetry.Run Proof)
    (modelRun : M → PV_L2_F3FullRetry.Run Proof)
    (realRows : R → Row → Obs) (modelRows : M → Row → Obs)
    (p : PV_L2_Premises join realRun modelRun realRows modelRows)
    (s : join.cp.S) (good : ¬(∃ i, bad old queries i (join.cp.toM s))) :
    realRows (join.cp.toR s) = modelRows (join.cp.toM s).1.1 := by
  funext row
  cases row
  exacts [p.V352 s good,p.V353 s good,p.V354 s good,p.V355 s good,
    p.V356 s good,p.V357 s good,p.V358 s good,p.V359 s good,p.V360 s good,
    p.V361 s good,p.V362 s good,p.V363 s good,p.V364 s good,p.V365 s good,
    p.V367 s good,p.V368 s good,p.V369 s good,p.V380_inversion s good]

/-- SAME coupling, same bad event, entire L1/retry/ROM record. No marginal
recoupling or added event charge occurs in the composition. This is a
conditional real-to-source result; simE absorption is still separate. -/
def extend (join : RunJoin runtime model old queries)
    (realRun : R → PV_L2_F3FullRetry.Run Proof)
    (modelRun : M → PV_L2_F3FullRetry.Run Proof)
    (realRows : R → Row → Obs) (modelRows : M → Row → Obs)
    (p : PV_L2_Premises join realRun modelRun realRows modelRows) :
    RunJoin (fun r => (runtime r,realRun r,realRows r))
      (fun m => (model m,modelRun m,modelRows m)) old queries where
  cp := join.cp
  agreement := by
    intro s good
    exact congrArg₂ Prod.mk (join.agreement s good)
      (congrArg₂ Prod.mk (p.V366 s good)
        (rows_agree join realRun modelRun realRows modelRows p s good))

theorem same_coupling (join : RunJoin runtime model old queries)
    (realRun : R → PV_L2_F3FullRetry.Run Proof)
    (modelRun : M → PV_L2_F3FullRetry.Run Proof)
    (realRows : R → Row → Obs) (modelRows : M → Row → Obs)
    (p : PV_L2_Premises join realRun modelRun realRows modelRows) :
    (extend join realRun modelRun realRows modelRows p).cp = join.cp := rfl

#print axioms rows_agree
#print axioms extend
#print axioms same_coupling
end R1Z.PV_L2_Premises
