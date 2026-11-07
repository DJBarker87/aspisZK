set_option autoImplicit false
namespace NMX_R3_RegistryBoolFive
/-- Five original guard positions, with the scalar equality kept symbolic. -/
theorem fold {A : Type} (a b c d : Bool) (p : Prop) [Decidable p] (bad good : A) :
 (if a then bad else if p then bad else if b then bad else if c then bad else if d then bad else good) =
 (if a || decide p || b || c || d then bad else good) := by
 cases a <;> cases b <;> cases c <;> cases d <;> by_cases h : p <;> simp only [h,↓reduceIte,decide_true,decide_false] <;> rfl
#print axioms fold
end NMX_R3_RegistryBoolFive
