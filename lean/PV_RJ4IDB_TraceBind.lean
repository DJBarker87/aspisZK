import PV_RJ4IDB_Decoder
set_option autoImplicit false
namespace PV_RJ4IDB
variable {A B C : Type}
def pure (a : A) : Trace A := ⟨[],.success a⟩
def prepend (es : List Event) (t : Trace A) : Trace A := ⟨es++t.events,t.terminal⟩
def bind (t : Trace A) (f : A → Trace B) : Trace B :=
 match t.terminal with
 | .success a => prepend t.events (f a)
 | .failure e => ⟨t.events,.failure e⟩
 | .panic p => ⟨t.events,.panic p⟩
 | .abort c => ⟨t.events,.abort c⟩
 | .diverge => ⟨t.events,.diverge⟩

theorem bind_prepend (es : List Event) (t : Trace A) (f : A → Trace B) :
 bind (prepend es t) f = prepend es (bind t f) := by
 cases t with | mk xs ex => cases ex <;> simp [bind,prepend,List.append_assoc]

theorem bind_assoc (t : Trace A) (f : A → Trace B) (g : B → Trace C) :
 bind (bind t f) g = bind t (fun a => bind (f a) g) := by
 cases t with
 | mk es ex => cases ex with
   | success a => exact bind_prepend es (f a) g
   | failure e => rfl
   | panic p => rfl
   | abort c => rfl
   | diverge => rfl

theorem bind_failure (es : List Event) (e : Bytes) (f : A → Trace B) :
 bind ⟨es,.failure e⟩ f = ⟨es,.failure e⟩ := rfl

theorem bind_divergence (es : List Event) (f : A → Trace B) :
 bind ⟨es,.diverge⟩ f = ⟨es,.diverge⟩ := rfl
#print axioms bind_prepend
#print axioms bind_assoc
#print axioms bind_failure
#print axioms bind_divergence
end PV_RJ4IDB
