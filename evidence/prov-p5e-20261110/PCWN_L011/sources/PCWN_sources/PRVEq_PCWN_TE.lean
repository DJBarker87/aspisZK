import Aeneas
open Aeneas Aeneas.Std Result
set_option linter.unusedVariables false
namespace PCWN_TE
/-- PCWN generic type-transport lemmas: an equivalence of element types lifts through the Aeneas Array / Vec / Slice carriers (all subtypes of List). -/
def arrEquiv {α β : Type} (e : α ≃ β) (N : Usize) : Std.Array α N ≃ Std.Array β N where
  toFun a := ⟨a.val.map e, by rw [List.length_map]; exact a.property⟩
  invFun b := ⟨b.val.map e.symm, by rw [List.length_map]; exact b.property⟩
  left_inv a := by
    apply Subtype.ext
    show List.map e.symm (List.map e a.val) = a.val
    simp [List.map_map, Equiv.symm_comp_self]
  right_inv b := by
    apply Subtype.ext
    show List.map e (List.map e.symm b.val) = b.val
    simp [List.map_map, Equiv.self_comp_symm]
#print axioms arrEquiv

def vecEquiv {α β : Type} (e : α ≃ β) : alloc.vec.Vec α ≃ alloc.vec.Vec β where
  toFun a := ⟨a.val.map e, by rw [List.length_map]; exact a.property⟩
  invFun b := ⟨b.val.map e.symm, by rw [List.length_map]; exact b.property⟩
  left_inv a := by
    apply Subtype.ext
    show List.map e.symm (List.map e a.val) = a.val
    simp [List.map_map, Equiv.symm_comp_self]
  right_inv b := by
    apply Subtype.ext
    show List.map e (List.map e.symm b.val) = b.val
    simp [List.map_map, Equiv.self_comp_symm]
#print axioms vecEquiv

def sliceEquiv {α β : Type} (e : α ≃ β) : Slice α ≃ Slice β where
  toFun a := ⟨a.val.map e, by rw [List.length_map]; exact a.property⟩
  invFun b := ⟨b.val.map e.symm, by rw [List.length_map]; exact b.property⟩
  left_inv a := by
    apply Subtype.ext
    show List.map e.symm (List.map e a.val) = a.val
    simp [List.map_map, Equiv.symm_comp_self]
  right_inv b := by
    apply Subtype.ext
    show List.map e (List.map e.symm b.val) = b.val
    simp [List.map_map, Equiv.self_comp_symm]
#print axioms sliceEquiv
end PCWN_TE
