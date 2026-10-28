import R1Z.PV_RunJoin_WeightMap46
set_option autoImplicit false
namespace R1Z.PV_RunJoin_WeightArray46
open Aeneas Aeneas.Std Result
open PV_B2_F_ConstructorCarrier (amap)
open PV_RunJoin_WeightMap46 (mapResult)

theorem comp {A B C : Type} {n : Usize} (f : A → B) (g : B → C) (a : Array A n) :
    amap g (amap f a)=amap (fun x => g (f x)) a := by
  apply Subtype.ext
  exact List.map_map

theorem id {A : Type} {n : Usize} (a : Array A n) : amap (fun x => x) a=a := by
  apply Subtype.ext
  exact List.map_id

theorem repeat {A B : Type} (n : Usize) (f : A → B) (x : A) :
    amap f (Array.repeat n x)=Array.repeat n (f x) := by
  apply Subtype.ext
  simp only [amap,Array.repeat,List.map_replicate]

theorem result_comp {A B C : Type} (f : A → B) (g : B → C) (r : Result A) :
    mapResult g (mapResult f r)=mapResult (fun x => g (f x)) r := by
  cases r <;> rfl

#print axioms comp
#print axioms id
#print axioms repeat
#print axioms result_comp
end R1Z.PV_RunJoin_WeightArray46
