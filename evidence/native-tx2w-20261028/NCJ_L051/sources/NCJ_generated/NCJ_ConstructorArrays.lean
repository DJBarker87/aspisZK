import NCJ_CellCanon
set_option autoImplicit false
namespace NCJ_ConstructorArrays
open Aeneas Aeneas.Std Result

def Holds {α : Type} {n : Usize} (P : α → Prop) (a : Array α n) : Prop := ∀ x∈a.val,P x

def put {α : Type} {n : Usize} (a : Array α n) (i : Nat) (x : α) : Array α n :=
  ⟨a.val.set i x,by simpa only [List.length_set] using a.property⟩

theorem update {α : Type} {n : Usize} (a : Array α n) (i : Usize) (x : α) (h : i.val< n.val) :
    Array.update a i x=ok (put a i.val x) := by
  simp [Array.update,put,show i.val< a.val.length by rw [a.property];exact h]

theorem canonical_put {α : Type} {n : Usize} (P : α → Prop) (a : Array α n)
    (i : Nat) (x : α) (h : Holds P a) (hx : P x) : Holds P (put a i x) :=
  NCJ_CellCanon.list_set P a.val i x h hx

theorem canonical_pick {α : Type} {n : Usize} (P : α → Prop) (a : Array α n)
    (i : Nat) (bound : i< n.val) (h : Holds P a) : P (NCJ_GuardExact.pick a i bound) := by
  apply h
  have hb : i< a.val.length := by rw [a.property];exact bound
  exact List.mem_of_getElem? (show a.val[i]?=some (NCJ_GuardExact.pick a i bound) by
    simp [NCJ_GuardExact.pick,hb])

theorem repeat {α : Type} (P : α → Prop) (n : Usize) (x : α) (hx : P x) :
    Holds P (Array.repeat n x) := by
  intro y hy
  simp only [Array.repeat,List.mem_replicate] at hy
  rcases hy with ⟨_,rfl⟩
  exact hx

#print axioms update
#print axioms canonical_put
#print axioms canonical_pick
#print axioms repeat
end NCJ_ConstructorArrays
