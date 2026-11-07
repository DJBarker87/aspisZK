import NMS_RowSpec242
set_option autoImplicit false
namespace NMS_LogMap
open Aeneas Aeneas.Std AdapterRw

def result {A B : Type} (f : A → B) : Result A → Result B
 | .ok a => .ok (f a)
 | .fail e => .fail e
 | .div => .div

def rust {A B : Type} (f : A → B) : core.result.Result A NMS_OwnedPackets.PE →
 core.result.Result B NMS_OwnedPackets.PE
 | .Ok a => .Ok (f a)
 | .Err e => .Err e

def run {E F A B : Type} (event : E → F) (value : A → B) (r : NJU_Log.Run E A) : NJU_Log.Run F B :=
 ⟨result value r.result,r.events.map event⟩

theorem result_id {A : Type} (r : Result A) : result id r = r := by cases r <;> rfl

theorem reply {A B : Type} (f : A → B) (r : Result (core.result.Result A NMS_OwnedPackets.PE)) :
 result (rust f) r = NMS_RowSpec242.mapReply f r := by
 cases r with
 | ok r => cases r <;> rfl
 | fail _ => rfl
 | div => rfl

theorem bind {E F A B C D : Type} (event : E → F) (value : A → C) (output : B → D)
 (m : NJU_Log.Run E A) (n : NJU_Log.Run F C)
 (k : A → NJU_Log.Run E B) (l : C → NJU_Log.Run F D)
 (first : run event value m = n)
 (next : ∀ a, run event output (k a) = l (value a)) :
 run event output (NJU_Log.bind m k) = NJU_Log.bind n l := by
 subst n
 cases m with
 | mk r events =>
  cases r with
  | fail _ => rfl
  | div => rfl
  | ok a =>
   change (NJU_Log.Run.mk (result output (k a).result) ((events ++ (k a).events).map event) : NJU_Log.Run F D) =
    NJU_Log.Run.mk (l (value a)).result (events.map event ++ (l (value a)).events)
   rw [←next a]
   simp only [run,List.map_append]

theorem flow {E F A B C D : Type} (event : E → F) (value : A → B)
 (p : core.ops.control_flow.ControlFlow C D)
 (yes : D → NJU_Log.Run E A) (no : C → NJU_Log.Run E A) :
 run event value (match p with | .Continue a => yes a | .Break b => no b) =
 match p with | .Continue a => run event value (yes a) | .Break b => run event value (no b) := by
 cases p <;> rfl

theorem ite_map {E F A B : Type} (event : E → F) (value : A → B)
 (p : Prop) [Decidable p] (a b : NJU_Log.Run E A) :
 run event value (if p then a else b) =
 if p then run event value a else run event value b := by split <;> rfl

#print axioms result_id
#print axioms reply
#print axioms bind
#print axioms flow
#print axioms ite_map
end NMS_LogMap
