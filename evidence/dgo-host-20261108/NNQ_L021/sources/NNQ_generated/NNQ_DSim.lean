import NNQ_Stage1
set_option autoImplicit false
noncomputable section
namespace AspisR1.NNQ_HostDigest
open Aeneas Aeneas.Std Result AspisR1PublicPreparation.PreparedHashCode
inductive DSim {A : Type} : Code A → Code A → Prop where
  | done (a : A) : DSim (.done a) (.done a)
  | step {B : Type} (r : Result B) (k1 k2 : B → Code A) (hk : ∀ b, DSim (k1 b) (k2 b)) :
      DSim (.step r k1) (.step r k2)
  | digest {H : Type} (D1 D2 : AspisR1PublicPreparation.aspis_core.Digest32 H) (h : H) (parts : Slice (Slice U8)) (k1 k2 : Array U8 32#usize → Code A)
      (hk : ∀ d, DSim (k1 d) (k2 d)) : DSim (.digest D1 h parts k1) (.digest D2 h parts k2)

theorem lowerP_dsim {A : Type} {c1 c2 : Code A} (h : DSim c1 c2) : SdkD_PrepareLower.lower c1 = SdkD_PrepareLower.lower c2 := by
  induction h with
  | done a => rfl
  | step r k1 k2 _ ih =>
    simp only [SdkD_PrepareLower.lower]
    congr 1
    funext b
    exact ih b
  | digest D1 D2 h parts k1 k2 _ ih =>
    simp only [SdkD_PrepareLower.lower]
    congr 1
    funext d
    exact ih d


theorem dsim_refl {A : Type} (c : Code A) : DSim c c := by
  induction c with
  | done a => exact .done a
  | step r k ih => exact .step r k k ih
  | digest D h p k ih => exact .digest D D h p k k ih

theorem dsim_bind {A B : Type} {p q : Code A} {f g : A → Code B}
    (h : DSim p q) (hk : ∀ a, DSim (f a) (g a)) : DSim (p >>= f) (q >>= g) := by
  induction h with
  | done a => exact hk a
  | step r k1 k2 _ ih => exact .step r _ _ ih
  | digest D1 D2 h p k1 k2 _ ih => exact .digest D1 D2 h p _ _ ih

theorem dsim_digest {H : Type} (D1 D2 : AspisR1PublicPreparation.aspis_core.Digest32 H)
    (h : H) (p : Slice (Slice U8)) : DSim (effects.digest D1 h p) (effects.digest D2 h p) :=
  .digest D1 D2 h p _ _ (fun d => .done d)

#print axioms lowerP_dsim
#print axioms dsim_refl
#print axioms dsim_bind
#print axioms dsim_digest
end AspisR1.NNQ_HostDigest
end
