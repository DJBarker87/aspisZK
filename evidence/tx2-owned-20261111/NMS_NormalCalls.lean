import NMS_NormalRefine
set_option autoImplicit false
namespace NMS_NormalCalls
open RSL NMS_NormalRefine

theorem call {A B : Type} (domain : A → Prop) (actual model : A → Spec B)
 (law : ∀ a, Normal (actual a) (model a)) (a : A) :
 Normal (Spec.call domain actual a) (Spec.call domain model a) := by
 intro env value events run
 exact ⟨run.1,law a env value events run.2⟩

 theorem seq {A : Type} {m n : RS Unit} {next later : RS A}
 (first : Normal m n) (last : Normal next later) : Normal (RS.seq m next) (RS.seq n later) :=
 rsbind first (fun _ => last)
#print axioms call
#print axioms seq
end NMS_NormalCalls
