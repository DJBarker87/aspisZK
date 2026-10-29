import Aeneas
import R1Z.PV_RDCD4_Zip194
namespace R1Z.PV_RDCD4_Wrappers194
set_option autoImplicit false

/-- The two source storage wrappers, including the writable return path. -/
structure MaybeDangling (A : Type) where
  value : A
  deriving Repr
structure ManuallyDrop (A : Type) where
  value : MaybeDangling A
  deriving Repr

def new {A : Type} (a : A) : ManuallyDrop A := ⟨⟨a⟩⟩

def project {A : Type} (w : ManuallyDrop A) : A × (A → ManuallyDrop A) :=
  (w.value.value,fun a => {w with value:={w.value with value:=a}})

/-- Apply the callee, then restore its changed value through BOTH wrappers. -/
def through {A B : Type} (f : A → B × A) (w : ManuallyDrop A) :
    B × ManuallyDrop A :=
  let (a,back) := project w
  let (r,a) := f a
  (r,back a)

theorem restore {A : Type} (w : ManuallyDrop A) :
    (project w).2 (project w).1=w := by cases w; rfl

theorem store {A : Type} (w : ManuallyDrop A) (a : A) :
    (project w).2 a=new a := rfl

theorem through_binding {A B : Type} (f : A → B × A) (w : ManuallyDrop A)
    (r : B) (a : A) (h : f w.value.value=(r,a)) :
    through f w=(r,new a) := by
  simp only [through,project,h,new]

theorem project_new {A : Type} (a : A) : (project (new a)).1=a := rfl

theorem identity {A : Type} (a : A) : id a=a := rfl

theorem zip_new_fields {A B : Type} (a : A) (b : B) :
    PV_RDCD4_Zip194.new a b=⟨a,b,0,0⟩ := rfl

theorem through_complete {A B : Type} (f : A → B × A) (w : ManuallyDrop A) :
    through f w=(let (r,a) := f w.value.value; (r,new a)) := rfl

#print axioms identity
#print axioms zip_new_fields
#print axioms through_complete
#print axioms restore
#print axioms store
#print axioms through_binding
#print axioms project_new
end R1Z.PV_RDCD4_Wrappers194
