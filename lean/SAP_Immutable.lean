import SAP_PrepareOwner
set_option autoImplicit false
noncomputable section
namespace AspisR1.SAP_Immutable
open Aeneas Aeneas.Std Result
open AspisR1CurrentCaller

/-- The preparation domain on the SAME actual run, with no immutable owner
hypothesis or second preparation witness. -/
theorem on_run {C H : Type} (ops : Ops) (reserved : Bool)
    (query : Port3_NativeQueryBody.Ops) (geo : Port3_NativeGeometryBody.Ops C)
    (B : AspisR1PublicPreparation.FinishModel.Boundaries) (std : ClaimsUnrolledFinish.StdCalls)
    (D : aspis_core.digest.Digest32 H) (hash : H)
    (pub : aspis_statement.pool_v1.pair_forest_semantic_terminal.r0.Public)
    (publicBytes proof : Slice U8) (split : Usize) (saved : alloc.vec.Vec U8)
    (run : Tx1Q_Execution.Run (Tx1Q_Execution.actual ops reserved query geo (F3M_CircleSource.install B) std)
      reserved query geo D hash pub publicBytes proof split saved) :
    Port5Q2_Prepared.PreparedFields (Tx1Q_Carriers.prepared run.p) := by
  exact (SAP_PrepareOwner.installed
    (Op3I_Install.install (Op4P_Install.install (Tx1Q_Execution.base ops reserved query geo))) B std).accepted
      D hash pub proof run.zero run.p run.scratch run.prepare_call

#print axioms on_run
end AspisR1.SAP_Immutable
end
