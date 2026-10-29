import R1Z.PV_RunJoin_QueryInRangeFailure57
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_QueryRangeObstruction57
open Aeneas Aeneas.Std Result ProverRwFull PV_RunJoin_WeightInstalled46
open PV_RunJoin_PublishSkeleton54

def poison [ExternalTypes] (p : prover.Publication) : prover.Publication :=
  { p with backend := {p.backend with c1 := some (PV_RunJoin_QueryEmptyWords57.broken p.tree), c2 := some (PV_RunJoin_QueryNativeObstruction56.unused p)}, queries := PV_RunJoin_QueryInRangeFailure57.queries }

theorem accepted (base : ExternalTypes) (heap : Heap) (box : Box)
    (ops : @ExternalFuns (types base)) :
    @aspis_core.r0.domain.FibreIndex.new (types base) (selected base heap box ops) 0#usize=ok (.Ok 0#usize) := by
  change @ExternalFuns.op75 (types base) (selected base heap box ops) 0#usize=_
  rw [PV_RunJoin_QueryIndexInstalled56.installed base heap box ops]
  simp only [ProverRwDictionaryDomain.fibreNew,show (0#usize)<262144#usize from by scalar_tac,if_true]

theorem failure (base : ExternalTypes) (heap : Heap) (box : Box)
    (ops : @ExternalFuns (types base)) (p : prover.Publication) (out : alloc.vec.Vec U8) :
    @prover.append_query_openings (types base) (selected base heap box ops) out
      (PV_RunJoin_QueryEmptyWords57.broken p.tree) (PV_RunJoin_QueryNativeObstruction56.unused p)
      PV_RunJoin_QueryInRangeFailure57.queries (alloc.vec.Vec.deref p.folded_word) p.folded_salts=fail .arrayOutOfBounds := by
  letI : ExternalTypes := types base
  letI : ExternalFuns := selected base heap box ops
  apply PV_RunJoin_QueryInRangeFailure57.source
    out p.tree (PV_RunJoin_QueryNativeObstruction56.unused p) _ p.folded_salts
    (ProverRwDictionaryTower.fromW AspisR1ProducerRelease47.field.wide_exact.WideExact.ZERO)
  · exact PV_RunJoin_EncoderFields49.zero base heap box ops
  · exact accepted base heap box ops

theorem complete {I : Type} (base : ExternalTypes) (heap : Heap) (box : Box)
    (ops : @ExternalFuns (types base)) (runs : I → @Run (types base)) (i : I)
    (p : prover.Publication)
    (hf : @Fields (types base) (selected base heap box ops) (runs i) p)
    (bound : (@Run.plan (types base) (runs i)).offOpenings≤Usize.max) :
    ¬@PV_RunJoin_PublishSkeleton57.PV_RunJoin_Link_QueryAppend
      (types base) (selected base heap box ops) I runs := by
  intro link
  have fields : @Fields (types base) (selected base heap box ops) (runs i) (poison p) := hf
  obtain ⟨next,success,_⟩ := (link i (poison p) fields PV_RunJoin_QueryInRangeFailure57.range).2
    (PV_RunJoin_QueryNativeObstruction56.buffer _ bound)
    (PV_RunJoin_QueryEmptyWords57.broken p.tree) (PV_RunJoin_QueryNativeObstruction56.unused p)
    rfl rfl (PV_RunJoin_QueryNativeObstruction56.buffer_length _ bound)
  have hf := failure base heap box ops p (PV_RunJoin_QueryNativeObstruction56.buffer _ bound)
  change @prover.append_query_openings (types base) (selected base heap box ops) _ _ _ _ _ _=ok next at success
  change @prover.append_query_openings (types base) (selected base heap box ops) _ _ _ _ _ _=fail .arrayOutOfBounds at hf
  change @prover.append_query_openings (types base) (selected base heap box ops)
    (PV_RunJoin_QueryNativeObstruction56.buffer _ bound)
    (PV_RunJoin_QueryEmptyWords57.broken p.tree) (PV_RunJoin_QueryNativeObstruction56.unused p)
    PV_RunJoin_QueryInRangeFailure57.queries (alloc.vec.Vec.deref p.folded_word) p.folded_salts=ok next at success
  rw [hf] at success
  cases success

#print axioms poison
#print axioms accepted
#print axioms failure
#print axioms complete
end R1Z.PV_RunJoin_QueryRangeObstruction57
