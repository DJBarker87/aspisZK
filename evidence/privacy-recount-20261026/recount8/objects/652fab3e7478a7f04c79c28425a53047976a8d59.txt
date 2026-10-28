import R1Z.PV_RunJoin_WeightMap46
set_option autoImplicit false
namespace R1Z.PV_RunJoin_WeightUpdate46
open Aeneas Aeneas.Std Result
open PV_B2_F_ConstructorCarrier (amap)
open PV_RunJoin_WeightMap46 (mapResult)

theorem complete {A B : Type} {n : Usize} (f : A → B) (a : Array A n)
    (j : Usize) (x : A) :
    Array.update (amap f a) j (f x)=mapResult (amap f) (Array.update a j x) := by
  have hget : (amap f a)[j]? = (a[j]?).map f := by
    change (a.val.map f)[j.val]?=(a.val[j.val]?).map f
    exact List.getElem?_map
  unfold Array.update
  rw [hget]
  cases h : a[j]? with
  | none => rfl
  | some y =>
    apply congrArg Result.ok
    apply Subtype.ext
    change (a.val.map f).set j.val (f x)=(a.val.set j.val x).map f
    exact (List.map_set ..).symm
#print axioms complete
end R1Z.PV_RunJoin_WeightUpdate46
