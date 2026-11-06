import NIX_HeapFrames
set_option autoImplicit false
namespace AspisR1.NIX_FlatGeometry

def word (p : Fin 3) (i : Fin 29) (limb : Fin 4) : Nat := 4*(29*p.val+i.val)+limb.val

theorem bounds (p : Fin 3) (i : Fin 29) (limb : Fin 4) : word p i limb<348 := by
 unfold word;omega

theorem injective (p q : Fin 3) (i j : Fin 29) (a b : Fin 4) :
 word p i a=word q j b ↔ p=q ∧ i=j ∧ a=b := by
 unfold word
 constructor
 · intro same
   have rows : p.val=q.val := by omega
   have columns : i.val=j.val := by omega
   exact ⟨Fin.ext rows,Fin.ext columns,Fin.ext (by omega)⟩
 · rintro ⟨rfl,rfl,rfl⟩;rfl

theorem disjoint (p q : Fin 3) (different : p≠q) (i j : Fin 29) (a b : Fin 4) :
 word p i a≠word q j b := fun h=>different ((injective p q i j a b).mp h).1

/-- A universally quantified observed word determines every nested row cell;
this composes the raw native observation windows without reading uninitialized cells. -/
theorem cell_ext {T : Type} (before after : Fin 3 → Fin 29 → Fin 4 → T)
 (observed : ∀ p i limb,after p i limb=before p i limb) : after=before := by
 funext p i limb;exact observed p i limb

#print axioms bounds
#print axioms injective
#print axioms disjoint
#print axioms cell_ext
end AspisR1.NIX_FlatGeometry
