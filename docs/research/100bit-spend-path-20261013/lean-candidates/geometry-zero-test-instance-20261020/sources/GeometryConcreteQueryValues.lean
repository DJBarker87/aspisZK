import GeometryInputsInverseComposition
import GeometryGroupingInverse
import R17QueryValuesActualAnyNonzeroV1
set_option autoImplicit false
open Aeneas Aeneas.Std Result
namespace AspisR1GeometryInputs.Proof
open alloc.vec R17CurrentM31Semantics

def concreteQueryValues (q : U32) : Result
    (core.result.Result ((Array M31 5#usize) × M31) GeometryInputsError) := do
  let r ← R17QueryValuesWholeBodyV21.emittedRawWithCallees
    R17QueryValuesWholeBodyStoredV1.actualSourceCallees R17SliceAnySourceV1.queryZeroAny q
  match r with
  | .Ok x => ok (.Ok x)
  | .Err _ => ok (.Err GeometryInputsError.Query)

private theorem bind_ok_inv {α β : Type} {r : Result α} {f : α → Result β}
    {x : β} (h : Bind.bind r f = .ok x) :
    ∃ a, r = .ok a ∧ f a = .ok x := by
  cases r with
  | ok a => exact ⟨a,rfl,h⟩
  | fail e => simp [Bind.bind] at h
  | div => simp [Bind.bind] at h

theorem concreteQueryValues_nonzero : NonzeroOutputs concreteQueryValues := by
  intro q values z h
  unfold concreteQueryValues at h
  rcases bind_ok_inv h with ⟨r,hr,h⟩
  cases r with
  | Err e => cases h
  | Ok x =>
    have he := core.result.Result.Ok.inj (Result.ok.inj h)
    subst x
    exact (R17QueryValuesActualAnyNonzeroV1.queryValuesEntry_zeroAny_success_nonzero q values z hr).2

theorem concrete_geometry_inverse_success (queries : Array U32 22#usize)
    (start end1 : Usize) (inverse zs : Vec M31)
    (h : geometryAndInvert concreteQueryValues queries start end1 = .ok (.Ok (inverse,zs))) :
    start.val ≤ end1.val ∧ end1.val ≤ 22 ∧
      AspisR1BatchBackward.Proof.CanonicalVec inverse ∧
      ∃ records : List InputRecord, InputTrace concreteQueryValues queries start.val end1.val records ∧
        inverse.val.map decode = ((records.flatMap (fun e => e.1.val)).map decode).map Inv.inv ∧
        zs.val = records.map Prod.snd ∧ records.length = end1.val-start.val ∧
        inverse.val.length = (end1.val-start.val)*5 ∧ zs.val.length = end1.val-start.val :=
  geometryAndInvert_success concreteQueryValues queries concreteQueryValues_nonzero start end1 inverse zs h

theorem concrete_grouping_success (queries : Array U32 22#usize)
    (start end1 : Usize) (inverse zs : Vec M31)
    (hrun : geometryAndInvert concreteQueryValues queries start end1 = .ok (.Ok (inverse,zs)))
    (i j : Usize) (hi : i.val < end1.val-start.val) (hj : j.val < 5)
    (x : M31) (capture : AspisR1GeometryGrouping.geometry_groups.closure.closure)
    (hcallback : AspisR1GeometryGrouping.geometry_groups.closure.closure.Insts.CoreOpsFunctionFnMutTupleUsizeM31.call_mut
      (inverse,i) j = .ok (x,capture)) :
    ∃ (records : List InputRecord) (hri : i.val<records.length),
      InputTrace concreteQueryValues queries start.val end1.val records ∧
      capture=(inverse,i) ∧
      decode x = (decode ((records[i.val]).1.val.getD j.val 0#u32))⁻¹ :=
  grouping_success_individual_inverse concreteQueryValues queries concreteQueryValues_nonzero
    start end1 inverse zs hrun i j hi hj x capture hcallback

#print axioms concreteQueryValues_nonzero
#print axioms concrete_geometry_inverse_success
#print axioms concrete_grouping_success
end AspisR1GeometryInputs.Proof
