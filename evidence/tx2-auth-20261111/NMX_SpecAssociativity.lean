import RSL_Base
set_option autoImplicit false
namespace NMX_SpecAssociativity
open RSL
/-- Source-order reassociation preserves returning prefixes and independently
stopped prefixes. No continuation after abort/divergence is postulated. -/
theorem bind {A B C : Type} (m : Spec A) (f : A → Spec B) (g : B → Spec C) :
 Spec.bind (Spec.bind m f) g = Spec.bind m (fun a => Spec.bind (f a) g) := by
 funext env o
 apply propext
 constructor
 · intro h
   rcases h with ⟨b,e1,o2,hmf,hg,ho⟩ | ⟨e1,hmf,ho⟩ | ⟨e1,hmf,ho⟩
   · rcases hmf with ⟨a,ea,of,hm,hf,he⟩ | ⟨_,_,he⟩ | ⟨_,_,he⟩
     · cases of with
       | mk exit ef =>
         cases he
         refine Or.inl ⟨a,ea,⟨o2.exit,ef ++ o2.events⟩,hm,
           Or.inl ⟨b,ef,o2,hf,hg,rfl⟩,?_⟩
         simpa only [List.append_assoc] using ho
     · cases he
     · cases he
   · rcases hmf with ⟨a,ea,of,hm,hf,he⟩ | ⟨e,hm,he⟩ | ⟨_,_,he⟩
     · cases of with
       | mk exit ef =>
         cases he
         exact Or.inl ⟨a,ea,⟨.abort,ef⟩,hm,Or.inr (Or.inl ⟨ef,hf,rfl⟩),ho⟩
     · cases he
       exact Or.inr (Or.inl ⟨_,hm,ho⟩)
     · cases he
   · rcases hmf with ⟨a,ea,of,hm,hf,he⟩ | ⟨_,_,he⟩ | ⟨e,hm,he⟩
     · cases of with
       | mk exit ef =>
         cases he
         exact Or.inl ⟨a,ea,⟨.diverge,ef⟩,hm,Or.inr (Or.inr ⟨ef,hf,rfl⟩),ho⟩
     · cases he
     · cases he
       exact Or.inr (Or.inr ⟨_,hm,ho⟩)
 · intro h
   rcases h with ⟨a,ea,tail,hm,hfg,ho⟩ | ⟨_,hm,ho⟩ | ⟨_,hm,ho⟩
   · rcases hfg with ⟨b,ef,o2,hf,hg,ht⟩ | ⟨ef,hf,ht⟩ | ⟨ef,hf,ht⟩
     · subst tail
       refine Or.inl ⟨b,ea ++ ef,o2,
         Or.inl ⟨a,ea,⟨.ret b,ef⟩,hm,hf,rfl⟩,hg,?_⟩
       simpa only [List.append_assoc] using ho
     · subst tail
       exact Or.inr (Or.inl ⟨ea ++ ef,Or.inl ⟨a,ea,⟨.abort,ef⟩,hm,hf,rfl⟩,ho⟩)
     · subst tail
       exact Or.inr (Or.inr ⟨ea ++ ef,Or.inl ⟨a,ea,⟨.diverge,ef⟩,hm,hf,rfl⟩,ho⟩)
   · exact Or.inr (Or.inl ⟨e,Or.inr (Or.inl ⟨e,hm,rfl⟩),ho⟩)
   · exact Or.inr (Or.inr ⟨e,Or.inr (Or.inr ⟨e,hm,rfl⟩),ho⟩)

theorem rust {A B C : Type} (m : RS A) (f : A → RS B) (g : B → RS C) :
 RS.bind (RS.bind m f) g = RS.bind m (fun a => RS.bind (f a) g) := by
 unfold RS.bind
 rw [bind]
 congr 1
 funext reply
 cases reply with
 | ok a => rfl
 | error e => rw [Spec.bind_pure]
#print axioms bind
#print axioms rust
end NMX_SpecAssociativity
