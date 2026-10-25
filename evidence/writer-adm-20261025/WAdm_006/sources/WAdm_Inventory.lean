import WAdm_Domain
set_option autoImplicit false
noncomputable section
open Aeneas Aeneas.Std Result
namespace AspisR1.WAdm_Inventory
open Tx1Q_Carriers CheckpointBytes3Namespaces

theorem on_run {CoreError H : Type} (installed : AspisR1CurrentCaller.Ops) (reserved : Bool)
    (query : Port3_NativeQueryBody.Ops) (geo : Port3_NativeGeometryBody.Ops CoreError)
    (D : AspisR1CurrentCaller.aspis_core.digest.Digest32 H) (hash : H)
    (semantic : AspisR1CurrentCaller.aspis_statement.pool_v1.pair_forest_semantic_terminal.r0.Public)
    (pub proof : Slice U8) (split : Usize) (saved : alloc.vec.Vec U8)
    (run : Tx1Q_Execution.Run installed reserved query geo D hash semantic pub proof split saved)
    (owner : WAdm_Domain.SessionAPrepare installed)
    (ports : Port5Q1_QueryPorts.SessionAPrimitives query) :
    ∃ fields : Port5Q2_Prepared.PreparedFields (prepared run.p),
    ∃ size : (accumulator {run.out with weights := ⟨run.flushed.val,run.flushed.property⟩}).weights.val.length = 64,
    CheckpointBytesBlocks.CanonicalFields
      (Port3_DecodeCoherence.inventory (prepared run.p)
        (accumulator {run.out with weights := ⟨run.flushed.val,run.flushed.property⟩}) size fields.queries) := by
  have fields := owner.accepted D hash semantic proof run.zero run.p run.scratch run.prepare_call
  have mutable := WAdm_Arithmetic.on_run installed reserved query geo D hash semantic pub proof split saved
    run ports fields.rho
  have control := Tx1Q_Control.fields installed reserved query geo D hash semantic pub proof split saved run
  have size : (accumulator {run.out with weights := ⟨run.flushed.val,run.flushed.property⟩}).weights.val.length = 64 := by
    simpa only [accumulator,vec,List.length_map] using control.2.2.2.1
  refine ⟨fields,size,fields.gamma,fields.kappa,?_,fields.rho,?_,?_,fields.claim,mutable.1,mutable.2,?_⟩
  · simpa only [Port3_DecodeCoherence.inventory,CheckpointBytesBody.fields,toPrepared,mapArray,List.getElem_map] using fields.alpha
  · simpa only [Port3_DecodeCoherence.inventory,CheckpointBytesBody.fields,toPrepared,mapArray,List.getElem_map] using fields.semanticAlpha
  · intro j
    have hc := fields.coordinates j
    fin_cases j <;> simpa only [Port3_DecodeCoherence.inventory,CheckpointBytesBody.fields,
      toPrepared,mapArray,List.getElem_map,toPoint] using hc
  · intro j
    simp only [Port3_DecodeCoherence.inventory,CheckpointBytesBody.fields,toAccumulator,
      mapVec,List.getElem_map]
    exact control.2.2.2.2 _ (List.getElem_mem _)

#print axioms on_run
end AspisR1.WAdm_Inventory
end
