import PV_B3_Copy_117_Funs
import R1Z.ProverRwP7CurrentFieldSource
namespace PV_B3_FieldTransport
open Aeneas Aeneas.Std Result
set_option autoImplicit false
namespace New
abbrev C := PV_B3_Copy_117.aspis_core.field.CM31
abbrev Q := PV_B3_Copy_117.aspis_core.field.QM31
end New
namespace Old
abbrev C := ProverRwFull.aspis_core.field.CM31
abbrev Q := ProverRwFull.aspis_core.field.QM31
end Old

def toC (x : New.C) : Old.C := ⟨x.a,x.b⟩
def fromC (x : Old.C) : New.C := ⟨x.a,x.b⟩
def toQ (x : New.Q) : Old.Q := ⟨toC x.c0,toC x.c1⟩
def fromQ (x : Old.Q) : New.Q := ⟨fromC x.c0,fromC x.c1⟩
theorem c_left (x : New.C) : fromC (toC x) = x := by cases x; rfl
theorem c_right (x : Old.C) : toC (fromC x) = x := by cases x; rfl
theorem q_left (x : New.Q) : fromQ (toQ x) = x := by cases x with | mk a b => cases a; cases b; rfl
theorem q_right (x : Old.Q) : toQ (fromQ x) = x := by cases x with | mk a b => cases a; cases b; rfl

def map {α β : Type} (f : α → β) : Result α → Result β
 | .ok x => .ok (f x)
 | .fail e => .fail e
 | .div => .div

theorem map_ok {α β : Type} (f : α → β) (x : α) : map f (.ok x) = .ok (f x) := rfl
theorem map_bind {α β γ : Type} (f : β → γ) (r : Result α) (g : α → Result β) :
 map f (r >>= g) = (r >>= fun x => map f (g x)) := by cases r <;> rfl

theorem map_comp {α β γ : Type} (f : α → β) (g : β → γ) (r : Result α) :
 map g (map f r) = map (fun x => g (f x)) r := by cases r <;> rfl

#print axioms c_left
#print axioms c_right
#print axioms q_left
#print axioms q_right
#print axioms map_bind
#print axioms map_comp
end PV_B3_FieldTransport
