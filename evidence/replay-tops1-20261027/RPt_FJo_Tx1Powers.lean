import RPt_FJo_SourceArray
set_option autoImplicit false
noncomputable section
namespace AspisR1.FJo_Tx1Powers
open Aeneas Aeneas.Std Result
open AspisR1CurrentCaller InstalledPreparation
open AspisR1ClaimPreparedBridge
/-- TX1's actual scratch, transported to the SAME prepared gamma. -/
theorem value {CoreError H : Type} (ops : Ops) (reserved : Bool)
    (query : Port3_NativeQueryBody.Ops) (geo : Port3_NativeGeometryBody.Ops CoreError)
    (B : AspisR1PublicPreparation.FinishModel.Boundaries) (std : ClaimsUnrolledFinish.StdCalls)
    (D : aspis_core.digest.Digest32 H) (hash : H)
    (pub : aspis_statement.pool_v1.pair_forest_semantic_terminal.r0.Public)
    (publicBytes proof : Slice U8) (split : Usize) (saved : alloc.vec.Vec U8)
    (run : Tx1Q_Execution.Run (Tx1Q_Execution.actual ops reserved query geo B std)
      reserved query geo D hash pub publicBytes proof split saved) :
    let g := FIp_DotsAdapter.toArray (Tx1Q_Carriers.arr Tx1Q_Carriers.e run.scratch)
    FIo_ArrayCanon.Holds g ∧ ∀ j : Fin 29,FIp_ArrayValue.value g j.val=
      CheckpointBytes5Output.ofE (Tx1Q_Carriers.prepared run.p).gamma^j.val := by
  obtain ⟨p,rs,output,scratch,canonical,cells⟩ := FJo_Tx1Scratch.value ops reserved query geo B std D hash
    pub publicBytes proof split saved run
  rw [←scratch,←output]
  exact FJo_SourceArray.value rs _ cells
#print axioms value
end AspisR1.FJo_Tx1Powers
end
