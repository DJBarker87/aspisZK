import Port5Q1_QueryPorts
import Port4C_RowStd
import Port4C_QueryValues
import Port3_NativeQueryFrame
set_option autoImplicit false
noncomputable section
namespace NEB_InstalledOpening
open Aeneas Aeneas.Std Result AspisR1 AspisR1Stage2
open Port3_NativeQueryBody

theorem same_return (ops : Ops) (proof : Slice U8) (p : verifier.Prepared)
    (a out : verifier.Accumulator)
    (g : Array aspis_core.field.wide_exact.WideExact 29#usize)
    (obs : Option (verifier.Phase → Result Unit)) (geometry : verifier.QueryGeometry)
    (b bout : verifier.BatchedWeights) (length : proof.val.length=57607)
    (o : Port4C_QueryValues.Observation
      (Port4C_RowStd.install (Port5Q1_QueryPorts.install ops))
      proof p a out g obs geometry b bout) :
    o.opening.val.length=832 ∧
      AspisV8R19.DuplexFrames.bytesOf o.opening.val=
        OraclePortCompactDraft.slice (AspisV8R19.DuplexFrames.bytesOf proof.val)
          (10055+a.next.val*832) 832 := by
  have bound := Port3_NativeQueryFrame.query_read_bound p a o.query o.query_read
  obtain ⟨view,run,len,bytes⟩ := Port4B_Opening.opening_exact proof length a.next bound
  have actual : Port4B_Opening.opening proof a.next=ok o.opening := o.opening_read
  have same : view=o.opening := Result.ok.inj (run.symm.trans actual)
  exact same ▸ ⟨len,bytes⟩

/-- The child opening domain is derived from the SAME successful query, not
an additional opening-return or length premise. -/
theorem accepted_query (ops : Ops) (proof : Slice U8) (p : verifier.Prepared)
    (a out : verifier.Accumulator)
    (g : Array aspis_core.field.wide_exact.WideExact 29#usize)
    (obs : Option (verifier.Phase → Result Unit)) (geometry : verifier.QueryGeometry)
    (b bout : verifier.BatchedWeights) (length : proof.val.length=57607)
    (accepted : verifier.candidate.query_values
      (Port4C_RowStd.install (Port5Q1_QueryPorts.install ops))
      proof p a g obs geometry b=ok (.Ok (out,bout))) :
    ∃ o : Port4C_QueryValues.Observation
      (Port4C_RowStd.install (Port5Q1_QueryPorts.install ops))
      proof p a out g obs geometry b bout,
      o.opening.val.length=832 := by
  obtain ⟨o⟩ := Port4C_QueryValues.observed _ proof p a out g obs geometry b bout accepted
  exact ⟨o,(same_return ops proof p a out g obs geometry b bout length o).1⟩

#print axioms same_return
#print axioms accepted_query
end NEB_InstalledOpening
end
