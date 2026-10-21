import S8JoinModelRepresentation

/-! Exact finish equivalence needs field equality of raw rows, not equality
of unreduced U64 storage. This is the source-state handoff to S7. -/
set_option autoImplicit false
noncomputable section
namespace AspisR1.S8JoinRawCongruence
open Aeneas Aeneas.Std Result
open AspisV8R15.ExactTowerBase
open S8OwnedP6ValueModel S8OwnedP6Finish S8JoinFinishField S8JoinModelRepresentation

theorem raw_mod_eq (a b : Row) (meaning : rawValue a=rawValue b) (k : Fin 4) :
    (rowAt a k).val%2147483647=(rowAt b k).val%2147483647 := by
  have h := congrArg (fun q : QM31Exact => (limb q k).val) meaning
  fin_cases k <;> simpa [limb,rawValue,M31Exact,P] using h

/-- Canonical reductions are literally equal, not merely equal as field values. -/
theorem modelValue_eq (a b : Row) (meaning : rawValue a=rawValue b) :
    modelValue a=modelValue b := by
  have cells (k : Fin 4) : coordinate (modelValue a) k=coordinate (modelValue b) k := by
    apply UScalar.eq_of_val_eq
    exact (modelValue_coordinates a k).1.trans
      ((raw_mod_eq a b meaning k).trans (modelValue_coordinates b k).1.symm)
  calc
    modelValue a = ⟨⟨coordinate (modelValue a) 0,coordinate (modelValue a) 1⟩,
        ⟨coordinate (modelValue a) 2,coordinate (modelValue a) 3⟩⟩ := by rfl
    _ = ⟨⟨coordinate (modelValue b) 0,coordinate (modelValue b) 1⟩,
        ⟨coordinate (modelValue b) 2,coordinate (modelValue b) 3⟩⟩ := by rw [cells,cells,cells,cells]
    _ = modelValue b := by rfl

/-- Arbitrary raw source representation of the same 64 field weights gives
exactly the canonical reference's finished list. Old destination contents do
not matter. Allocation/query/checkpoint provenance remains S7's obligation. -/
theorem output_eq (source : Raw) (destination : Weights) (w : Fin 64 → QM31Exact)
    (size : destination.length=64) (lengths : destination.length≤source.length)
    (meaning : ∀ (l : Fin 64) r, source.val[l.val]?=some r → rawValue r=w l) :
    S8JoinFinishExact.output source destination=
      S8JoinFinishExact.output (raw w) old := by
  apply Subtype.ext
  apply List.ext_getElem?
  intro j
  by_cases bound : j<64
  · have hs : j<source.val.length := by change destination.val.length=64 at size; change destination.val.length≤source.val.length at lengths; omega
    let r := source.val[j]
    have read : source.val[j]?=some r := List.getElem?_eq_getElem hs
    have eq := modelValue_eq r (S8JoinModelRepresentation.row (w ⟨j,bound⟩)) ((meaning ⟨j,bound⟩ r read).trans (row_field _).symm)
    have index : j<destination.length := by omega
    simp only [S8JoinFinishExact.output,List.getElem?_map,List.getElem?_take,
      if_pos index,read,Option.map_some,raw,old,alloc.vec.Vec.length,List.length_replicate]
    rw [if_pos bound,List.getElem?_ofFn,dif_pos bound]
    exact congrArg some eq
  · have h64 : 64≤source.val.length := by
      change destination.val.length=64 at size
      change destination.val.length≤source.val.length at lengths
      omega
    have len1 : (S8JoinFinishExact.output source destination).val.length=64 := by
      simp [S8JoinFinishExact.output,size,Nat.min_eq_left h64]
    have len2 : (S8JoinFinishExact.output (raw w) old).val.length=64 := by
      simp [S8JoinFinishExact.output,raw,old]
    rw [List.getElem?_eq_none (by omega),List.getElem?_eq_none (by omega)]

/-- Exact whole emitted reference equality under the minimal reached field relation. -/
theorem finish_eq (source : Raw) (destination : Weights) (w : Fin 64 → QM31Exact)
    (size : destination.length=64) (lengths : destination.length≤source.length)
    (meaning : ∀ (l : Fin 64) r, source.val[l.val]?=some r → rawValue r=w l) :
    S8OwnedP6.finish_owned source destination=S8OwnedP6.finish_owned (raw w) old := by
  rw [S8JoinFinishExact.reference_exact source destination lengths,
    S8JoinFinishExact.reference_exact (raw w) old (by simp [raw,old]),
    output_eq source destination w size lengths meaning]

#print axioms raw_mod_eq
#print axioms modelValue_eq
#print axioms output_eq
#print axioms finish_eq
end AspisR1.S8JoinRawCongruence
end
