import AspisR1S9ActualWeightsNewBoxNewV3.Funs
import S9ConstructorV3Loop2InnerCanonicalV1
import S9ConstructorV3StatementCellCanonicalV1
import S9ConstructorV3QMMulCanonicalV1
import S9ConstructorV3QMAddSubCanonicalV1
import S9CandidateFoldMapPrimitivesV1
import S9PairArrayUpdateCanonicalV1

set_option autoImplicit false
open Aeneas Aeneas.Std Result ControlFlow
namespace AspisR1S9ConstructorV3SuccessorCarryBodyCanonicalV1
open AspisR1S9ConstructorV3Loop2InnerCanonicalV1

abbrev Vector := Array Q 10#usize
abbrev ReverseRange := core.iter.adapters.rev.Rev R

def mapVector (a : Vector) : Array ProbeQ 10#usize :=
  AspisR1S9CandidateFoldMapPrimitivesV1.mapArray toProbeQ a

def VectorCanonical (a : Vector) : Prop :=
  ∀ (i : Usize) (v : ProbeQ), Array.index_usize (mapVector a) i = .ok v → CanQ v

theorem raw_read_canonical (a : Vector) (i : Usize) (q : Q)
    (ha : VectorCanonical a) (hread : Array.index_usize a i = .ok q) : CanQ (toProbeQ q) := by
  have hmap := AspisR1S9CandidateFoldMapPrimitivesV1.mapArray_index_result toProbeQ a i
  rw [hread] at hmap
  exact ha i (toProbeQ q) hmap.symm

/-- Same-execution inversion of the actual reverse carry-loop body. -/
theorem carry_body_success_has_execution
    (z successor successorOut : Vector) (iter iterNext : ReverseRange)
    (carry carryOut : Q)
    (hbody : AspisR1S9ActualWeightsNewBoxNewV3.state_only_prefix.state_only_statement_points_loop.body
      z iter successor carry = .ok (.cont (iterNext, successorOut, carryOut))) :
    ∃ (coordinate : Usize) (bit product sum twice cell : Q),
      core.iter.adapters.rev.Rev.Insts.CoreIterTraitsIteratorIterator.next
        (core.ops.range.Range.Insts.DoubleEndedIterator core.iter.range.StepUsize) iter =
          .ok (some coordinate, iterNext) ∧
      Array.index_usize z coordinate = .ok bit ∧
      AspisR1S9ActualWeightsNewBoxNewV3.field.QM31.mul bit carry = .ok product ∧
      AspisR1S9ActualWeightsNewBoxNewV3.field.QM31.add bit carry = .ok sum ∧
      AspisR1S9ActualWeightsNewBoxNewV3.field.QM31.add product product = .ok twice ∧
      AspisR1S9ActualWeightsNewBoxNewV3.field.QM31.sub sum twice = .ok cell ∧
      Array.update successor coordinate cell = .ok successorOut ∧ product = carryOut := by
  unfold AspisR1S9ActualWeightsNewBoxNewV3.state_only_prefix.state_only_statement_points_loop.body at hbody
  obtain ⟨next, hnext, hbody⟩ := bind_success_inv _ _ _ hbody
  rcases next with ⟨opt, iter1⟩
  cases opt with
  | none =>
    change ok (ControlFlow.done successor : ControlFlow (ReverseRange × Vector × Q) Vector) =
      ok (ControlFlow.cont (iterNext, successorOut, carryOut) :
        ControlFlow (ReverseRange × Vector × Q) Vector) at hbody
    cases hbody
  | some coordinate =>
    obtain ⟨bit, hbit, hbody⟩ := bind_success_inv (Array.index_usize z coordinate) _ _ hbody
    obtain ⟨product, hproduct, hbody⟩ := bind_success_inv
      (AspisR1S9ActualWeightsNewBoxNewV3.field.QM31.mul bit carry) _ _ hbody
    obtain ⟨sum, hsum, hbody⟩ := bind_success_inv
      (AspisR1S9ActualWeightsNewBoxNewV3.field.QM31.add bit carry) _ _ hbody
    obtain ⟨twice, htwice, hbody⟩ := bind_success_inv
      (AspisR1S9ActualWeightsNewBoxNewV3.field.QM31.add product product) _ _ hbody
    obtain ⟨cell, hcell, hbody⟩ := bind_success_inv
      (AspisR1S9ActualWeightsNewBoxNewV3.field.QM31.sub sum twice) _ _ hbody
    obtain ⟨out, hupdate, hbody⟩ := bind_success_inv
      (Array.update successor coordinate cell) _ _ hbody
    have hstate := ControlFlow.cont.inj (Result.ok.inj hbody)
    have hiEq : iter1 = iterNext := congrArg Prod.fst hstate
    have hsEq : out = successorOut := congrArg (fun s => s.2.1) hstate
    have hcEq : product = carryOut := congrArg (fun s => s.2.2) hstate
    subst iterNext
    subst successorOut
    exact ⟨coordinate, bit, product, sum, twice, cell,
      hnext, hbit, hproduct, hsum, htwice, hcell, hupdate, hcEq⟩

theorem carry_body_success_canonical
    (z successor successorOut : Vector) (iter iterNext : ReverseRange)
    (carry carryOut : Q)
    (hz : VectorCanonical z) (hs : VectorCanonical successor) (hc : CanQ (toProbeQ carry))
    (hbody : AspisR1S9ActualWeightsNewBoxNewV3.state_only_prefix.state_only_statement_points_loop.body
      z iter successor carry = .ok (.cont (iterNext, successorOut, carryOut))) :
    VectorCanonical successorOut ∧ CanQ (toProbeQ carryOut) := by
  obtain ⟨coordinate, bit, product, sum, twice, cell,
      hnext, hbit, hproduct, hsum, htwice, hcell, hupdate, hcEq⟩ :=
    carry_body_success_has_execution z successor successorOut iter iterNext carry carryOut hbody
  have hb := raw_read_canonical z coordinate bit hz hbit
  have hproductCan := AspisR1S9ConstructorV3QMMulCanonicalV1.generated_mul_success_canonical
    bit carry product hb hc hproduct
  have hsumCan : CanQ (toProbeQ sum) := by
    simpa only [toProbeQ, AspisR1S9ConstructorV3QMAddSubCanonicalV1.toProbeQM] using
      AspisR1S9ConstructorV3QMAddSubCanonicalV1.qm_add_success_canonical bit carry sum hb hc hsum
  have htwiceCan : CanQ (toProbeQ twice) := by
    simpa only [toProbeQ, AspisR1S9ConstructorV3QMAddSubCanonicalV1.toProbeQM] using
      AspisR1S9ConstructorV3QMAddSubCanonicalV1.qm_add_success_canonical
        product product twice hproductCan hproductCan htwice
  have hcellCan : CanQ (toProbeQ cell) := by
    simpa only [toProbeQ, AspisR1S9ConstructorV3QMAddSubCanonicalV1.toProbeQM] using
      AspisR1S9ConstructorV3QMAddSubCanonicalV1.qm_sub_success_canonical
        sum twice cell hsumCan htwiceCan hcell
  have hbound := AspisR1S9ConstructorV3StatementCellCanonicalV1.update_success_bound
    successor coordinate cell successorOut hupdate
  have hout := AspisR1S9PairArrayUpdateCanonicalV1.update_preserves_canonical_reads
    toProbeQ CanQ successor coordinate cell successorOut hbound hupdate hs hcellCan
  refine ⟨hout, ?_⟩
  rw [hcEq] at hproductCan
  change CanQ (toProbeQ carryOut) at hproductCan
  exact hproductCan

#print axioms carry_body_success_canonical
end AspisR1S9ConstructorV3SuccessorCarryBodyCanonicalV1
