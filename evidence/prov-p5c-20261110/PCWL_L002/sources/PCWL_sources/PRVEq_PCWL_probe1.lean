import Aeneas
open Aeneas Aeneas.Std Result ControlFlow Error
set_option maxHeartbeats 200000
namespace PRVEq_PCWL

def arrEquiv {α β : Type} {N : Usize} (e : α ≃ β) : Std.Array α N ≃ Std.Array β N where
  toFun a := ⟨a.val.map e, by rw [List.length_map]; exact a.property⟩
  invFun b := ⟨b.val.map e.symm, by rw [List.length_map]; exact b.property⟩
  left_inv a := by apply Subtype.ext; simp [List.map_map, Function.comp_def]
  right_inv b := by apply Subtype.ext; simp [List.map_map, Function.comp_def]

def vecEquiv {α β : Type} (e : α ≃ β) : alloc.vec.Vec α ≃ alloc.vec.Vec β where
  toFun a := ⟨a.val.map e, by rw [List.length_map]; exact a.property⟩
  invFun b := ⟨b.val.map e.symm, by rw [List.length_map]; exact b.property⟩
  left_inv a := by apply Subtype.ext; simp [List.map_map, Function.comp_def]
  right_inv b := by apply Subtype.ext; simp [List.map_map, Function.comp_def]

def sliceEquiv {α β : Type} (e : α ≃ β) : Std.Slice α ≃ Std.Slice β where
  toFun a := ⟨a.val.map e, by rw [List.length_map]; exact a.property⟩
  invFun b := ⟨b.val.map e.symm, by rw [List.length_map]; exact b.property⟩
  left_inv a := by apply Subtype.ext; simp [List.map_map, Function.comp_def]
  right_inv b := by apply Subtype.ext; simp [List.map_map, Function.comp_def]

end PRVEq_PCWL

#print axioms PRVEq_PCWL.arrEquiv
#print axioms PRVEq_PCWL.vecEquiv
#print axioms PRVEq_PCWL.sliceEquiv
