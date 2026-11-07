import NMS_RSLSuccess
set_option autoImplicit false
namespace NMS_NormalRefine
open RSL
/-- Normal observations include BOTH Rust Ok and Rust Err. The definition
adds no totality assumption and says nothing false about an abort suffix. -/
def Normal {A : Type} (actual model : Spec A) : Prop :=
 ∀ env value events, actual env ⟨.ret value,events⟩ → model env ⟨.ret value,events⟩

theorem refl {A : Type} (m : Spec A) : Normal m m := fun _ _ _ h => h

theorem bind {A B : Type} {actual model : Spec A} {next later : A → Spec B}
 (first : Normal actual model) (rest : ∀ a, Normal (next a) (later a)) :
 Normal (Spec.bind actual next) (Spec.bind model later) := by
 intro env value events run
 obtain ⟨a,e1,e2,h1,h2,same⟩ := NMS_RSLSuccess.bind_return _ _ _ _ _ run
 exact Or.inl ⟨a,e1,⟨.ret value,e2⟩,first env a e1 h1,rest a env value e2 h2,
  by cases same; rfl⟩

theorem rsbind {A B : Type} {actual model : RS A} {next later : A → RS B}
 (first : Normal actual model) (rest : ∀ a, Normal (next a) (later a)) :
 Normal (RS.bind actual next) (RS.bind model later) := by
 apply bind first
 intro reply
 cases reply with
 | ok a => exact rest a
 | error e => exact refl _

#print axioms refl
#print axioms bind
#print axioms rsbind
end NMS_NormalRefine
