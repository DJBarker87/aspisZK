import NEV_AccumulatePrefix
import NEV_TailModel
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace NEV_AccumulateComplete
open Aeneas Aeneas.Std Result NEV_AccumulateCarriers
open AspisR1 AspisR1Stage2 Port3_NativeQueryBody

theorem reference_split (base : Ops) (p : verifier.Prepared) (a : verifier.Accumulator)
    (node : U32) (value : NBF_RowInstall.E) (b : verifier.BatchedWeights) :
    AspisR1Stage2.verifier.accumulateWithOps (NBO_AccumulateAssociation.reference (NEV_TailModel.fields base))
      p a node value b =
      (do let middle ← NBO_AccumulateAssociation.prefixRun (NEV_TailModel.fields base) a node b
          NEV_TailModel.tail p a value middle) := by
  unfold AspisR1Stage2.verifier.accumulateWithOps NBO_AccumulateAssociation.reference
    NBO_AccumulateAssociation.prefixRun NEV_TailModel.tail
  simp only [NBO_AccumulateAssociation.sourceOps,NBF_Accumulate.install,
    NBF_RowInstall.install,NBF_BasisInstall.install,NEV_TailModel.fields,bind_assoc_eq,bind_tc_ok]

/-- Complete actual emitted function to the retained adopted accumulation,
with a concrete field dictionary proved in NEV_PrimitiveBindings. Every full
record field and Result tag is retained. There is no successful-run premise. -/
theorem reference (base : Ops) (p : NEV_AccumulateRaw.Prepared) (a : NEV_AccumulateRaw.Accumulator)
    (node : U32) (value : RawE) (b : NEV_AccumulateRaw.BatchedWeights)
    (width : a.weights.val.length=64) (raw : b.raw.val.length=64) (global : a.next.val<22)
    (hv : NBO_TailDomain.WideCanonical (toE value))
    (hr : NBO_TailDomain.WideCanonical (toE a.rhs))
    (hp : NBF_PowerStep.Canonical (toQ a.power))
    (hq : NBF_PowerStep.Canonical (toQ p.rho)) :
    (do let out ← NEV_AccumulateRaw.accumulate_batched_with_node p a node value b
        ok (NEV_TailModel.toPair out)) =
      AspisR1Stage2.verifier.accumulateWithOps (NBO_AccumulateAssociation.reference (NEV_TailModel.fields base))
        (toPrepared p) (toAccumulator a) node (toE value) (toWeights b) := by
  rw [NEV_AccumulateTail.source_cut,reference_split]
  rw [← NEV_AccumulatePrefix.association (NEV_TailModel.fields base) a node b width raw global]
  simp only [bind_assoc_eq,bind_tc_ok]
  have continuations :
      (fun middle : NEV_AccumulateRaw.BatchedWeights =>
        do let out ← NEV_AccumulateTail.tail p a value middle;ok (NEV_TailModel.toPair out)) =
      (fun middle : NEV_AccumulateRaw.BatchedWeights =>
        NEV_TailModel.tail (toPrepared p) (toAccumulator a) (toE value) (toWeights middle)) := by
    funext middle
    exact NEV_TailModel.association p a value middle hv hr hp hq
  exact congrArg (fun next : NEV_AccumulateRaw.BatchedWeights →
      Result (verifier.Accumulator × verifier.BatchedWeights) =>
    do let middle ← NEV_AccumulateTail.rows a node b;next middle) continuations

/-- The already-proved NEI independent-counter theorem supplies the exact
native checked/wrapping join, including TX2's distinct local term counter. -/
theorem native (base : Ops) (p : NEV_AccumulateRaw.Prepared) (a : NEV_AccumulateRaw.Accumulator)
    (node : U32) (value : RawE) (b : NEV_AccumulateRaw.BatchedWeights)
    (width : a.weights.val.length=64) (raw : b.raw.val.length=64)
    (global : a.next.val<22) (localActive : b.terms.val<22)
    (hv : NBO_TailDomain.WideCanonical (toE value))
    (hr : NBO_TailDomain.WideCanonical (toE a.rhs))
    (hp : NBF_PowerStep.Canonical (toQ a.power))
    (hq : NBF_PowerStep.Canonical (toQ p.rho)) :
    (do let out ← NEV_AccumulateRaw.accumulate_batched_with_node p a node value b
        ok (NEV_TailModel.toPair out)) =
      verifier.accumulate_batched_with_node
        (NBO_AccumulateAssociation.sourceOps (NEV_TailModel.fields base))
        (toPrepared p) (toAccumulator a) node (toE value) (toWeights b) := by
  have mappedWidth : (toAccumulator a).weights.val.length=64 := by
    simpa only [toAccumulator,mapVec,List.length_map] using width
  exact (reference base p a node value b width raw global hv hr hp hq).trans
    (NEI_AccumIndependentCounters.independent_counters (NEV_TailModel.fields base)
      (toPrepared p) (toAccumulator a) node (toE value) (toWeights b)
      mappedWidth raw global localActive).symm
#print axioms reference_split
#print axioms reference
#print axioms native
end NEV_AccumulateComplete
end
