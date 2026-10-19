import CuSavingsRhoScalar
import CuSavingsSuffixMap

/-! Concrete partial-fold carrier and mutable iterator handback model for the
actual emitted flush loop. The generic suffix-map lemma supplies its structural
step; no concrete four-step term is normalized. -/
set_option autoImplicit false
namespace AspisR1.CuSavingsRhoFlushModel
open Aeneas Aeneas.Std Result ControlFlow
open AspisR1CuRho
open AspisV8R17.RawReducer
open AspisR1.CuSavingsSuffixMap
abbrev Iter := Aeneas.Std.core.slice.iter.IterMut U64

def foldWord (x : U64) : U64 :=
  UScalar.ofNatCore (foldBits x.val) (by
    have h := first_fold_lt x.val x.bv.isLt
    change foldBits x.val < 18446744073709551616
    omega)

theorem foldWord_val (x : U64) : (foldWord x).val = foldBits x.val := rfl

theorem foldWord_execution (x : U64) :
    AspisR1.ExtractedCurrentReducer.foldExecution x = .ok (foldWord x) := by
  obtain ⟨out,hr,hv⟩ := AspisR1.ExtractedCurrentReducer.foldExecution_success x
  have heq : out = foldWord x := UScalar.eq_of_val_eq hv
  simpa only [heq] using hr

def modelIter (iter : Iter) : Iter :=
  {slice := ⟨suffixMap foldWord iter.i iter.slice.val,by
      rw [length_suffixMap];exact iter.slice.property⟩
   i := iter.slice.val.length}

theorem model_at_end (iter : Iter) (hend : iter.i = iter.slice.val.length) :
    modelIter iter = iter := by
  cases iter with
  | mk values position =>
    change position = values.val.length at hend
    subst position
    unfold modelIter
    congr 1
    apply Subtype.ext
    exact suffixMap_at_length foldWord values.val

theorem model_step (iter : Iter) (hi : iter.i < iter.slice.val.length) :
    {modelIter {iter with i := iter.i+1} with
      slice := (modelIter {iter with i := iter.i+1}).slice.setAtNat iter.i
        (foldWord (iter.slice.val[iter.i]'hi))} = modelIter iter := by
  cases iter with
  | mk values position =>
    simp only [modelIter]
    congr 1
    apply Subtype.ext
    simp only [Slice.setAtNat]
    exact suffixMap_step foldWord position values.val hi

theorem source_body_step (iter next : Iter) (back : Iter → Iter) (limb : U64)
    (nextBack : Iter → Option U64 → Iter)
    (hnext : Aeneas.Std.core.slice.iter.IteratorIterMut.next iter =
      .ok (some limb,next,nextBack)) :
    verifier.BatchedWeights.push_loop1.body iter back =
      .ok (.cont (next,fun out => back (nextBack out (some (foldWord limb))))) := by
  simp only [verifier.BatchedWeights.push_loop1.body,hnext,bind_tc_ok,lift]
  change (do
    let high ← UScalar.shiftRight limb 31
    let value ← UScalar.add (UScalar.and limb AspisR1.ExtractedCurrentReducer.mask64) high
    Result.ok (ControlFlow.cont (next,fun out => back (nextBack out (some value))) :
      ControlFlow (Iter × (Iter → Iter)) (Iter × (Iter → Iter)))) = _
  have hfold := foldWord_execution limb
  have h := congrArg (fun run : Result U64 => do
    let value ← run
    Result.ok (ControlFlow.cont (next,fun out => back (nextBack out (some value))) :
      ControlFlow (Iter × (Iter → Iter)) (Iter × (Iter → Iter)))) hfold
  simpa only [AspisR1.ExtractedCurrentReducer.foldExecution,bind_assoc_eq,bind_tc_ok] using h

#print axioms foldWord_execution
#print axioms model_at_end
#print axioms model_step
#print axioms source_body_step
end AspisR1.CuSavingsRhoFlushModel
