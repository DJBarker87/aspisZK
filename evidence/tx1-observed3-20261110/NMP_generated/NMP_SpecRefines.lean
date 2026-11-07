import NMP_CanonicalPackets
set_option autoImplicit false
namespace AspisR1.NMP_SpecRefines
open RSL

def Refines {A : Type} (m n : Spec A) : Prop := ∀ env o,m env o → n env o

theorem bind {A B : Type} (m n : Spec A) (k l : A → Spec B)
 (head : Refines m n) (tail : ∀ a,Refines (k a) (l a)) :
 Refines (Spec.bind m k) (Spec.bind n l) := by
 intro env o h
 rcases h with ⟨a,e,o2,hm,hk,ho⟩ | ⟨e,hm,ho⟩ | ⟨e,hm,ho⟩
 · exact Or.inl ⟨a,e,o2,head env _ hm,tail a env _ hk,ho⟩
 · exact Or.inr (Or.inl ⟨e,head env _ hm,ho⟩)
 · exact Or.inr (Or.inr ⟨e,head env _ hm,ho⟩)

theorem result_bind {E A B : Type} (m n : RE E A) (k l : A → RE E B)
 (head : Refines m n) (tail : ∀ a,Refines (k a) (l a)) :
 Refines (RE.bind m k) (RE.bind n l) := by
 unfold RE.bind
 apply bind _ _ _ _ head
 intro r
 cases r with
 | error e => intro env o h;exact h
 | ok a => exact tail a

#print axioms bind
#print axioms result_bind
end AspisR1.NMP_SpecRefines
