import R1Z.PV_RunJoin_ActualPlanProjection60
import R1Z.PV_RunJoin_ClaimFields48
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_FinishStored63
open Aeneas Aeneas.Std Result ProverRwFull PV_RunJoin_WeightInstalled46
open PV_RunJoin_PublishSkeleton54

theorem inactive (base : ExternalTypes) (heap : Heap) (box : Box)
    (ops : @ExternalFuns (types base)) (phase : @PV_RunJoin_NativeControl55.Phase (types base))
    (p : prover.Publication)
    (context : @PV_RunJoin_PublishContext57.QueryContext (types base) (selected base heap box ops)
      (@PV_RunJoin_ActualRun.runs (types base) (selected base heap box ops) phase) p) :
    letI : ExternalTypes := types base
    letI : ExternalFuns := selected base heap box ops
    ∃ ib, aspis_core.field.wide_exact.WideExact.to_le_bytes p.inactive=ok ib ∧
      bytes ib.val=(PV_RunJoin_ActualRun.plans phase).inactive := by
  letI : ExternalTypes := types base
  letI : ExternalFuns := selected base heap box ops
  let ib := PV_RunJoin_FlatBytes35.wire p.inactive
  have hib : aspis_core.field.wide_exact.WideExact.to_le_bytes p.inactive=ok ib :=
    PV_RunJoin_ClaimFields48.serializer base heap box ops p.inactive
  obtain ⟨out,ho,hv⟩ := PV_RunJoin_CloneBytes43.complete (Array.to_slice ib)
  have he : (do let encoded ← aspis_core.field.wide_exact.WideExact.to_le_bytes p.inactive
                let slice ← Aeneas.Std.lift (Array.to_slice encoded)
                alloc.slice.Slice.to_vec core.clone.CloneU8 slice)=ok out := by
    simp only [hib,lift,bind_tc_ok,ho]
  have hp := PV_RunJoin_ActualPublication60.projection phase p context
    (fun publication => do
      let encoded ← aspis_core.field.wide_exact.WideExact.to_le_bytes publication.inactive
      let slice ← Aeneas.Std.lift (Array.to_slice encoded)
      alloc.slice.Slice.to_vec core.clone.CloneU8 slice) out he
  refine ⟨ib,hib,?_⟩
  change bytes ib.val=PV_RunJoin_ActualPlanSources59.publicationBytes phase _
  rw [hp,hv]

#print axioms inactive
end R1Z.PV_RunJoin_FinishStored63
