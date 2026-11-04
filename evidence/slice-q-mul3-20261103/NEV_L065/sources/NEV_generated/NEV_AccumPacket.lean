import NEV_AccumulateComplete
import NEV_PushDomains
import NEV_BasisCallDomains
set_option autoImplicit false
noncomputable section
namespace NEV_AccumPacket
open Aeneas Aeneas.Std Result NEV_AccumulateCarriers
open AspisR1 AspisR1Stage2 Port3_NativeQueryBody

/-- Input-only packet domain. In particular, no successful child, basis,
row traversal, field result, or complete accumulation result is assumed. -/
structure Domain (p : NEV_AccumulateRaw.Prepared) (a : NEV_AccumulateRaw.Accumulator)
    (value : RawE) (b : NEV_AccumulateRaw.BatchedWeights) : Prop where
 width : a.weights.val.length=64
 global : a.next.val<22
 localActive : b.terms.val<22
 valueCanonical : NBO_TailDomain.WideCanonical (toE value)
 rhsCanonical : NBO_TailDomain.WideCanonical (toE a.rhs)
 powerCanonical : NBF_PowerStep.Canonical (toQ a.power)
 rhoCanonical : NBF_PowerStep.Canonical (toQ p.rho)
 progress : S7JoinRowsTrace.Progress b.terms.val 0 (Port3_RowsInstall.toBW (toWeights b))

theorem raw_length (p : NEV_AccumulateRaw.Prepared) (a : NEV_AccumulateRaw.Accumulator)
    (value : RawE) (b : NEV_AccumulateRaw.BatchedWeights) (domain : Domain p a value b) :
    b.raw.val.length=64 := domain.progress.2.1

/-- Complete modeled Result/state/ordered-effect relation. This ghost state
is external to the returned owned vectors; their actual native mutable frame
is checked separately by the native cut/callee certificates. -/
theorem result_state_effects {S Event : Type} (state : S) (base : Ops)
    (p : NEV_AccumulateRaw.Prepared) (a : NEV_AccumulateRaw.Accumulator)
    (node : U32) (value : RawE) (b : NEV_AccumulateRaw.BatchedWeights)
    (domain : Domain p a value b) :
    (do let out ← NEV_AccumulateRaw.accumulate_batched_with_node p a node value b
        ok (NEV_TailModel.toPair out,state,([] : List Event))) =
      (do
        let out ← AspisR1Stage2.verifier.accumulateWithOps
            (NBO_AccumulateAssociation.reference (NEV_TailModel.fields base))
            (toPrepared p) (toAccumulator a) node (toE value) (toWeights b)
        ok (out,state,([] : List Event))) := by
  have same := NEV_AccumulateComplete.reference base p a node value b domain.width
    (raw_length p a value b domain) domain.global domain.valueCanonical domain.rhsCanonical
    domain.powerCanonical domain.rhoCanonical
  have lifted := congrArg (fun result : Result (verifier.Accumulator × verifier.BatchedWeights) =>
    do let out ← result;ok (out,state,([] : List Event))) same
  simpa only [bind_assoc_eq,bind_tc_ok] using lifted

/-- Any residual base dictionary fields are unreachable by this actual
function. The chosen concrete field/row/basis callbacks determine the result. -/
theorem no_base_dependency (first second : Ops)
    (p : NEV_AccumulateRaw.Prepared) (a : NEV_AccumulateRaw.Accumulator)
    (node : U32) (value : RawE) (b : NEV_AccumulateRaw.BatchedWeights)
    (domain : Domain p a value b) :
    AspisR1Stage2.verifier.accumulateWithOps
      (NBO_AccumulateAssociation.reference (NEV_TailModel.fields first))
      (toPrepared p) (toAccumulator a) node (toE value) (toWeights b) =
    AspisR1Stage2.verifier.accumulateWithOps
      (NBO_AccumulateAssociation.reference (NEV_TailModel.fields second))
      (toPrepared p) (toAccumulator a) node (toE value) (toWeights b) := by
  exact (NEV_AccumulateComplete.reference first p a node value b domain.width
    (raw_length p a value b domain) domain.global domain.valueCanonical domain.rhsCanonical
    domain.powerCanonical domain.rhoCanonical).symm.trans
    (NEV_AccumulateComplete.reference second p a node value b domain.width
      (raw_length p a value b domain) domain.global domain.valueCanonical domain.rhsCanonical
      domain.powerCanonical domain.rhoCanonical)
#print axioms raw_length
#print axioms result_state_effects
#print axioms no_base_dependency
end NEV_AccumPacket
end
