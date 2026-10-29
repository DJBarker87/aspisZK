import PV_L2E_TraceMachine
set_option autoImplicit false
noncomputable section
namespace PV_L2E_CommonSample
open R1Z R0Z.FsStatement PV_L2E

/-- Same common sample, same old/seed/fuel complement. This is still a
conditional specification: `honest` must be successful canonical preparation,
the machines must be source-bound, and initial must be D163's invariant.
No independent coupling or acceptance-only domain is substituted. -/
theorem on_existing_join {R M V S T E P : Type} [Fintype R] [Fintype M]
    {runtime : R → V} {model : M → V}
    {old : Fin 8 → M → Prop}
    {queries : M → List ProverCommitSeedEvent19.Entry}
    (join : ProverCommitFuelJoin22.RunJoin runtime model old queries)
    (native : Machine S E) (simulator : Machine T E)
    (Related : S → T → Prop) (honest : R → Prop)
    (realInit : R → S) (pubData : R → P)
    (simInit : P → ((M × OracleAnswer) × ProverCommitFuelJoin22.Tape) → T)
    (initial : ∀ s, honest (join.cp.toR s) →
      PV_FIB_Restricted.OffCharged old queries (join.cp.toM s) →
      Related (realInit (join.cp.toR s))
        (simInit (pubData (join.cp.toR s)) (join.cp.toM s)))
    (v353 : PV_L2E_Link_V353 native simulator Related)
    (v354 : PV_L2E_Link_V354 native simulator Related)
    (v355 : PV_L2E_Link_V355 native simulator Related)
    (v356 : PV_L2E_Link_V356 native simulator Related)
    (v357 : PV_L2E_Link_V357 native simulator Related)
    (v358 : PV_L2E_Link_V358 native simulator Related)
    (v359 : PV_L2E_Link_V359 native simulator Related)
    (v360 : PV_L2E_Link_V360 native simulator Related)
    (v361 : PV_L2E_Link_V361 native simulator Related)
    (v362 : PV_L2E_Link_V362 native simulator Related)
    (v363 : PV_L2E_Link_V363 native simulator Related)
    (v364 : PV_L2E_Link_V364 native simulator Related)
    (v365 : PV_L2E_Link_V365 native simulator Related)
    (v367 : PV_L2E_Link_V367 native simulator Related)
    (s : join.cp.S) (hs : honest (join.cp.toR s))
    (good : PV_FIB_Restricted.OffCharged old queries (join.cp.toM s)) :
    ∀ n, tracePrefix native n (realInit (join.cp.toR s)) =
      tracePrefix simulator n (simInit (pubData (join.cp.toR s)) (join.cp.toM s)) := by
  exact PV_L2E.trace_simulatable native simulator Related
    (fun s => PV_FIB_Restricted.OffCharged old queries (join.cp.toM s))
    (fun s => honest (join.cp.toR s))
    (fun s => realInit (join.cp.toR s)) (fun s => pubData (join.cp.toR s))
    join.cp.toM simInit initial
    v353 v354 v355 v356 v357 v358 v359 v360 v361 v362 v363 v364 v365 v367 s hs good

#print axioms on_existing_join
end PV_L2E_CommonSample
