import R1Z.PV_RunJoin_WeightCarrier46
set_option autoImplicit false
namespace R1Z.PV_RunJoin_WeightMap46
open Aeneas Aeneas.Std Result
open PV_B2_F_ConstructorCarrier (amap)
abbrev mapResult {A B : Type} (f : A → B) (r : Result A) : Result B :=
  PV_B2_E_OrdinaryOriginal.mapResult f r

theorem map_bind {A B C D : Type} (f : A → B) (g : C → D)
    (r : Result A) (k : A → Result C) (l : B → Result D)
    (h : ∀ a, mapResult g (k a)=l (f a)) :
    mapResult g (r >>= k)=(mapResult f r >>= l) := by
  cases r with
  | fail e => rfl
  | div => rfl
  | ok a => exact h a

theorem index {A B : Type} {n : Usize} (f : A → B) (a : Array A n) (j : Usize) :
    Array.index_usize (amap f a) j=mapResult f (Array.index_usize a j) := by
  unfold Array.index_usize amap
  simp only [List.getElem?_map]
  cases a.val[j.val]? <;> rfl

theorem update {A B : Type} {n : Usize} (f : A → B) (a : Array A n)
    (j : Usize) (x : A) :
    Array.update (amap f a) j (f x)=mapResult (amap f) (Array.update a j x) := by
  unfold Array.update
  split
  · rfl
  · apply congrArg Result.ok
    apply Subtype.ext
    change (a.val.map f).set j.val (f x)=(a.val.set j.val x).map f
    simp only [List.map_set]

#print axioms map_bind
#print axioms index
#print axioms update
end R1Z.PV_RunJoin_WeightMap46
