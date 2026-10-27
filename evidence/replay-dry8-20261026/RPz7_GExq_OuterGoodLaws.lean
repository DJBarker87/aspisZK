import RPz7_GExq_OuterLower
set_option autoImplicit false
noncomputable section
namespace AspisR1.GExq_OuterGoodLaws
open Aeneas Aeneas.Std Result S2W_Trace GExq_OuterLower
variable (hashv : SdkC_Source.Parts → Result SdkC_Source.Digest)

theorem pure_good {A : Type} (a : A) : Good hashv (pure a : Code A) := trivial

theorem lift_good {A : Type} (r : Result A) : Good hashv (monadLift r : Code A) := by
  cases r <;> trivial

theorem bind_good {A B : Type} (p : Code A) (k : A → Code B)
    (hp : Good hashv p) (hk : ∀ a, Good hashv (k a)) : Good hashv (p >>= k) := by
  induction p with
  | done a => exact hk a
  | step r c ih => cases r with
    | ok a => exact ih a hp
    | fail e => trivial
    | div => trivial
  | call op c ih => exact ⟨hp.1,fun a => ih a (hp.2 a)⟩

theorem lift_bind_good {A B : Type} (r : Result A) (k : A → Code B)
    (hk : ∀ a, Good hashv (k a)) : Good hashv ((monadLift r : Code A) >>= k) :=
  bind_good hashv _ _ (lift_good hashv r) hk

theorem call_good {A : Type} (call : Call A) (valid : GExq_ChildCode.Admissible hashv call) :
    Good hashv (perform call) := ⟨valid,fun _ => trivial⟩

theorem call_bind_good {A B : Type} (call : Call A) (k : A → Code B)
    (valid : GExq_ChildCode.Admissible hashv call) (hk : ∀ a, Good hashv (k a)) :
    Good hashv (perform call >>= k) := bind_good hashv _ _ (call_good hashv call valid) hk

#print axioms pure_good
#print axioms lift_good
#print axioms bind_good
#print axioms lift_bind_good
#print axioms call_good
#print axioms call_bind_good
end AspisR1.GExq_OuterGoodLaws
end
