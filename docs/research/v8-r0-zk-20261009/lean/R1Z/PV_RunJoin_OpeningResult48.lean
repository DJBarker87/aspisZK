import R1Z.PV_RunJoin_WeightResult46
import R1Z.ProverRwDictionaryTower
set_option autoImplicit false
namespace R1Z.PV_RunJoin_OpeningResult48
open Aeneas Aeneas.Std Result
open PV_RunJoin_WeightMap46 (mapResult)

theorem tower {A B : Type} (f : A → B) (r : Result A) :
    ProverRwDictionaryTower.mapResult f r=mapResult f r := by cases r <;> rfl

theorem bind_map {A B C : Type} (f : A → B) (r : Result A) (k : B → Result C) :
    (mapResult f r >>= k)=(r >>= fun x => k (f x)) := by cases r <;> rfl

theorem map_after {A B C : Type} (f : B → C) (r : Result A) (k : A → Result B) :
    mapResult f (r >>= k)=(r >>= fun x => mapResult f (k x)) := by cases r <;> rfl

theorem congr_map {A B C : Type} (f : A → B) (g : B → A) (h : ∀ a,g (f a)=a)
    (r : Result A) (k : A → Result C) :
    (mapResult f r >>= fun b => k (g b))=(r >>= k) := by
  rw [bind_map]
  apply congrArg (Aeneas.Std.bind r)
  funext a
  rw [h a]
#print axioms tower
#print axioms bind_map
#print axioms map_after
#print axioms congr_map
end R1Z.PV_RunJoin_OpeningResult48
