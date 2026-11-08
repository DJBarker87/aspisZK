set_option autoImplicit false
namespace PV_LIB

/-- Child laws are graphs of functions, never permissive native relations. -/
def Graph {A B : Type} (model : A → B) (a : A) (b : B) : Prop := b = model a

theorem graph_unique {A B : Type} (model : A → B) (a : A) (b c : B)
    (hb : Graph model a b) (hc : Graph model a c) : b = c := hb.trans hc.symm

/-- A process abort exposes only its event prefix. -/
inductive Observation (Value State Event : Type) where
  | returned : Value → State → List Event → Observation Value State Event
  | abort : List Event → Observation Value State Event

theorem abort_state_free {V S E : Type} (events : List E) (s t : S) :
    (fun (_ : S) => (Observation.abort events : Observation V S E)) s =
      (fun (_ : S) => (Observation.abort events : Observation V S E)) t := rfl

#print axioms graph_unique
#print axioms abort_state_free
end PV_LIB
