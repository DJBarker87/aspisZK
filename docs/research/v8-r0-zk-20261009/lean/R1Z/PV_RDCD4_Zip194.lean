import Aeneas
namespace R1Z.PV_RDCD4_Zip194
set_option autoImplicit false

/-- All fields of the deployed general-default Zip implementation. index and
len are unused by next but remain part of its state. -/
structure State (A B : Type) where
  a : A
  b : B
  index : Nat
  len : Nat
  deriving Repr

def new {A B : Type} (a : A) (b : B) : State A B := ⟨a,b,0,0⟩

/-- Expanded general-default macro: a.next()? precedes b.next()?. In the
second None case a is already advanced. No random-access specialization. -/
def next {A B X Y : Type} (nextA : A → Option X × A)
    (nextB : B → Option Y × B) (s : State A B) : Option (X×Y) × State A B :=
  let (x,a) := nextA s.a
  match x with
  | none => (none,{s with a:=a})
  | some x =>
    let (y,b) := nextB s.b
    match y with
    | none => (none,{s with a:=a,b:=b})
    | some y => (some (x,y),{s with a:=a,b:=b})

theorem first_none {A B X Y : Type} (f : A → Option X × A)
    (g : B → Option Y × B) (s : State A B) (a : A) (h : f s.a=(none,a)) :
    next f g s=(none,{s with a:=a}) := by
  simp only [next,h]

theorem second_none {A B X Y : Type} (f : A → Option X × A)
    (g : B → Option Y × B) (s : State A B) (x : X) (a : A) (b : B)
    (ha : f s.a=(some x,a)) (hb : g s.b=(none,b)) :
    next f g s=(none,{s with a:=a,b:=b}) := by
  simp only [next,ha,hb]

theorem both_some {A B X Y : Type} (f : A → Option X × A)
    (g : B → Option Y × B) (s : State A B) (x : X) (y : Y) (a : A) (b : B)
    (ha : f s.a=(some x,a)) (hb : g s.b=(some y,b)) :
    next f g s=(some (x,y),{s with a:=a,b:=b}) := by
  simp only [next,ha,hb]

#print axioms first_none
#print axioms second_none
#print axioms both_some
end R1Z.PV_RDCD4_Zip194
