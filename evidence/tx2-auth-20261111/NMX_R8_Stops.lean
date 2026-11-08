import NMX_R6_Observation
set_option autoImplicit false
namespace NMX_R8_Stops
open RSL

def diverge {A : Type} : Spec A := fun _ o => o = ⟨.diverge,[]⟩

theorem panic_bind {A B : Type} (k : A → Spec B) : Spec.bind Spec.panic k = Spec.panic := by
 funext env o
 apply propext
 simp [Spec.bind,Spec.panic]

theorem diverge_bind {A B : Type} (k : A → Spec B) : Spec.bind diverge k = diverge := by
 funext env o
 apply propext
 simp [Spec.bind,diverge]
#print axioms panic_bind
#print axioms diverge_bind
end NMX_R8_Stops
