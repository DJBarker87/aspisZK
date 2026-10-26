import JFn_DotsSlot
import JFo_QueryIndex
set_option autoImplicit false
noncomputable section
namespace AspisR1.JFn_DotsBoundary
open Aeneas Aeneas.Std Result
open AspisR1Stage2 Port3_NativeQueryBody

def rejecting (seed : Ops) : Ops := {seed with op20:=fun _ _ => fail .panic}

/-- Counterexample to acceptance uniformly over the remaining free seed.
It is NOT a counterexample to the real dot body, release, or actual fixture. -/
theorem query_rejects (seed : Ops) (g : Array SAQ_WideABI.E 29#usize)
    (geometry : verifier.QueryGeometry) (pending : verifier.BatchedWeights) :
    verifier.candidate.query_values (JFn_ArrayBuilder.ops (rejecting seed))
      JFx_NativeBytes.proof JFo_Prepared.value JFo_Prepared.accumulator g none geometry pending=fail .panic := by
  have query : Array.index_usize JFo_Prepared.value.queries JFo_Prepared.accumulator.next=ok 132355#u32 :=
    JFo_QueryIndex.source _ _ (by decide) 132355#u32 rfl
  have opening : (JFn_ArrayBuilder.ops (rejecting seed)).op11
      JFx_NativeBytes.proof JFo_Prepared.accumulator.next=ok (JFo_Opening.value ⟨10,by decide⟩) :=
    JFo_Opening.call ⟨10,by decide⟩
  unfold verifier.candidate.query_values
  rw [query,bind_tc_ok]
  simp only [lift,bind_tc_ok]
  rw [opening,bind_tc_ok]
  have dots : (JFn_ArrayBuilder.ops (rejecting seed)).op20 (JFo_Opening.value ⟨10,by decide⟩) g=fail .panic := by
    rw [JFn_DotsSlot.retained]
    rfl
  rw [dots,bind_tc_fail]

#print axioms query_rejects
end AspisR1.JFn_DotsBoundary
end
