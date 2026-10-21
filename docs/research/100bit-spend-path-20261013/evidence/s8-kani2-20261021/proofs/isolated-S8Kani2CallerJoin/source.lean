import S8Kani2FinishReferenceJoin

/-! Exact handoff to the S7/R15 caller. These premises concern the reached
raw vector and its mathematical sum, not a free S8 boundary proposition. -/
set_option autoImplicit false
noncomputable section
namespace S8Kani2CallerJoin
open Aeneas Aeneas.Std Result
open S8OwnedP6ValueModel S8OwnedP6Finish
open S8Kani2MutableValue S8Kani2FinishReferenceJoin
open S8Kani2MutableExtraction.batched_weights

def coordinate (q : F.Q) (j : Fin 4) : U32 :=
  match j.val with | 0 => q.c0.a | 1 => q.c0.b | 2 => q.c1.a | _ => q.c1.b

/-- The caller must supply this from the actual query/checkpoint execution.
No phase/canonicality restriction is needed by finish itself. -/
structure CallerInvariant (raw : Raw) (old : Weights)
    (sum : Nat → Fin 4 → Nat) : Prop where
  lengths : old.length≤raw.length
  congruence : ∀ j row, raw.val[j]?=some row → ∀ k : Fin 4,
    (rowAt row k).val%2147483647=sum j k%2147483647

theorem coordinate_transport (q : Q) (j : Fin 4) :
    coordinate (toFinish q) j=S8OwnedP6ValueModel.coordinate q j := by
  fin_cases j <;> rfl

/-- Once S7/R15 supply the reached raw congruence and lengths, the entire
mutable finalization yields the intended reduced sums in every coordinate. -/
theorem finish_caller_join (raw : Raw) (old : Weights) (terms : Usize)
    (sum : Nat → Fin 4 → Nat) (caller : CallerInvariant raw old sum) :
    ∃ out : FinishSlice,
      BatchedWeights.finish (⟨raw,terms⟩ : F.BW) (toSlice old)=.ok out ∧
      ∀ i : Usize, i.val<old.length → ∃ q : F.Q,
        Slice.index_usize out i=.ok q ∧
        ∀ k : Fin 4, (coordinate q k).val=sum i.val k%2147483647 ∧
          (coordinate q k).val<2147483647 := by
  obtain ⟨refOut,sourceOut,_,_,hsource,hcells⟩ :=
    finish_reference_simulation raw old terms caller.lengths
  refine ⟨sourceOut,hsource,?_⟩
  intro i hi
  obtain ⟨row,hrow,_,hread⟩ := hcells i hi
  refine ⟨toFinish (modelValue row),hread,?_⟩
  intro k
  rw [coordinate_transport]
  have hm := modelValue_coordinates row k
  exact ⟨hm.1.trans (caller.congruence i.val row hrow k),hm.2⟩

/-- A named, concrete P6 certificate at the finish boundary. Its reference
and mutable-traversal components are supplied; caller provenance remains
an explicit implication, to be instantiated by the reached S7/R15 state. -/
structure P6Certificate : Prop where
  reference : S8OwnedP6Certificate.ReferenceCertificate
  finish_simulation : ∀ raw old terms, old.length≤raw.length →
    ∃ referenceOut : Weights, ∃ sourceOut : FinishSlice,
      S8OwnedP6.finish_owned raw old=.ok referenceOut ∧
      referenceOut.length=old.length ∧
      BatchedWeights.finish (⟨raw,terms⟩ : F.BW) (toSlice old)=.ok sourceOut ∧
      ∀ i : Usize, i.val<old.length → ∃ row : Row,
        raw.val[i.val]?=some row ∧
        referenceOut.val[i.val]?=some (modelValue row) ∧
        Slice.index_usize sourceOut i=.ok (toFinish (modelValue row))

theorem p6_certificate : P6Certificate :=
  ⟨S8OwnedP6Certificate.reference_model,finish_reference_simulation⟩

#print axioms coordinate_transport
#print axioms finish_caller_join
#print axioms p6_certificate
end S8Kani2CallerJoin
