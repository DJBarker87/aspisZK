import Aeneas
set_option autoImplicit false
namespace PCI_IteTransport
universe u

theorem nested {T : Sort u} (p : Prop) [Decidable p] (test : Bool) (yes no : T) :
    (if (if p then test else false) then yes else no)=
      if p then (if test then yes else no) else no := by
  by_cases h : p <;> simp only [h,ite_true,ite_false,Bool.false_eq_true]

theorem decided {T : Sort u} (p : Prop) [Decidable p] (yes no : T) :
    (if decide p then yes else no)=(if p then yes else no) := by
  by_cases h : p <;> simp only [h,decide_true,decide_false,ite_true,ite_false,Bool.false_eq_true]

end PCI_IteTransport
#print axioms PCI_IteTransport.nested
#print axioms PCI_IteTransport.decided
