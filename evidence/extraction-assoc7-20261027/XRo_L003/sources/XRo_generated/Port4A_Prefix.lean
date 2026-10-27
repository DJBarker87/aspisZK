import Port3_NativeWriterShape
import Port3_NativeQueryTerms
set_option autoImplicit false
noncomputable section
namespace AspisR1.Port4A_Prefix
open Aeneas Aeneas.Std Result VTop_Stages
variable {CoreError W : Type}
abbrev installed := @Port3_NativeWriterShape.installed

theorem reached_calls (base : Ops) (reserved : Bool)
    (batch : Port3_NativeBatchBody.Ops)
    (geometryOps : Port3_NativeGeometryBody.Ops CoreError) (queryOps : Port3_NativeQueryBody.Ops)
    (finish : AspisR1Stage2.Stage2Finish.FinishOps W)
    {Hash : Type} (D : aspis_core.digest.Digest32 Hash) (hash : Hash)
    (semantic : aspis_statement.pool_v1.pair_forest_semantic_terminal.r0.Public)
    (proof : Slice U8) (split : Usize)
    (p : verifier.Prepared) (a : verifier.Accumulator)
    (reached : VTop_Provenance.WriterPrefix (installed base reserved batch geometryOps queryOps finish)
      D hash semantic proof split none p a) :
    ∃ (initial : verifier.Accumulator) (pending : verifier.BatchedWeights)
      (returned : verifier.Accumulator × verifier.BatchedWeights)
      (g : Array aspis_core.field.wide_exact.WideExact 29#usize)
      (geometry : verifier.QueryGeometry),
      initial.next.val=0 ∧ pending.terms=initial.next ∧
      Port2_QueryLoop.Calls
        (fun a b => Port3_NativeQueryBody.verifier.candidate.query_values
          (Port3_QueryStage.release (Port3_NativeRowFrame.install queryOps))
          proof p a g none geometry b) 10 initial pending returned.1 returned.2 10 ∧
      returned.2.terms.val=10 ∧ a.rhs=returned.1.rhs ∧
      a.power=returned.1.power ∧ a.next=returned.1.next := by
  obtain ⟨zero,g,prep,initial,root,geometry,pending,returned,flushed,parsed,sv,
    hs,hsv,hparse,hscan,hzero,hprep,hbranch,hinit,hbatch,hgeom,hpending,hquery,hflush,
    hw,hr,hp,hn⟩ := reached
  have hsplit : split.val = 10 := by
    have e : (10#usize : Usize) = sv := Result.ok.inj hs
    subst sv
    exact hsv
  have hi : Port3_Initial.constructor reserved .S2 = ok (.Ok initial) := by
    change Port3_Constructor.extracted (Port3_Constructor.leaves reserved) .S2 = _ at hinit
    rw [Port3_Constructor.normalization] at hinit
    exact hinit
  have initialFields := Port3_Initial.accepted_fields base reserved initial hi
  have initialSize : initial.weights.val.length=64 := by rw [initialFields.2.1,List.length_replicate]
  have pendingFields := Port3_NativePendingInstall.accepted_fields reserved initial.weights.deref pending
    initialSize hpending
  have pendingSize : pending.raw.val.length=64 := pendingFields.2.2.2
  have native := (Port3_QueryInstall.success_iff _ _).mp hquery
  have start : initial.next.val=0 := by rw [initialFields.2.2.2.2]; rfl
  have sync : pending.terms=initial.next := by
    rw [pendingFields.2.2.1,initialFields.2.2.2.2]
  have bound : initial.next.val≤split.val := by omega
  have terms := Port3_NativeQueryTerms.loop_terms (Port3_QueryStage.release queryOps)
    proof p initial returned.1 g none geometry pending returned.2 split
    initialSize pendingSize sync bound native
  rw [Port3_NativeQueryFrame.loop_eq] at native
  have calls := Port2_QueryLoop.source_calls
    (Port3_NativeQueryBody.verifier.candidate.query_values
      (Port3_QueryStage.release (Port3_NativeRowFrame.install queryOps)))
    proof p g none geometry split
    (fun a a1 b b1 h => (Port3_NativeQueryFrame.query_fields _
      proof p a a1 g none geometry b b1 h).2.2)
    initial returned.1 pending returned.2 bound native
  refine ⟨initial,pending,returned,g,geometry,start,sync,?_,?_,hr,hp,hn⟩
  · simpa only [hsplit,start,Nat.sub_zero] using calls
  · exact terms.2.trans hsplit

#print axioms reached_calls
end AspisR1.Port4A_Prefix
end
