import PFin_FirstHit
set_option autoImplicit false
noncomputable section
namespace AspisR1.PFin_CollisionTransport
open FS FS2 FS2.Duplex AspisV8PairedCommitment
variable {I A : Type} [DecidableEq I] [Fintype A] [Inhabited A]

/-- Read containment plus preservation of first-read order is sufficient.
Containment alone is false, as checked in PFin_CollisionOrder. -/
theorem ordered {B : Nat} (iv : A) (pred : Fin B → I → Option A) (H : I → A)
    (old larger : List (I × A)) (q r : Nat)
    (oldCons : ∀ x∈old,x.2=H x.1) (largerCons : ∀ x∈larger,x.2=H x.1)
    (support : ∀ a,Read old a → Read larger a)
    (order : ∀ a b,Before old a b → Read old b → Before larger a b)
    (budget : firstReads emptyTable larger≤r)
    (hit : hitsBad (AllAddressCollision.bad iv pred q) emptyTable old) :
    hitsBad (AllAddressCollision.bad iv pred r) emptyTable larger := by
  obtain ⟨a,read,miss,small,cause⟩ := PFin_FirstHit.exists_first _ H old emptyTable oldCons hit
  have beforeOfDefined (b : I) (defined : tableBefore emptyTable old a b≠none) : Before old b a := by
    rw [tableBefore_eq H old emptyTable a b oldCons] at defined
    by_contra absent
    exact defined (by rw [if_neg absent];rfl)
  apply FS.hitsBad_of_first _ H a larger emptyTable largerCons (support a read) rfl
  refine ⟨AllAddressCollisionTrace.small_before_read H larger a largerCons (support a read) r budget,?_⟩
  rcases cause with ivHit | ⟨b,previous⟩ | ⟨j,b,position,target⟩
  · exact Or.inl ivHit
  · have before := beforeOfDefined b (by rw [previous];exact Option.some_ne_none _)
    have values : H b=H a := by
      have equality : some (H b)=some (H a) := by
        simpa only [tableBefore_eq H old emptyTable a b oldCons,if_pos before] using previous
      exact Option.some.inj equality
    refine Or.inr (Or.inl ⟨b,?_⟩)
    rw [tableBefore_eq H larger emptyTable a b largerCons,if_pos (order b a before read),values]
  · refine Or.inr (Or.inr ⟨j,b,?_,target⟩)
    rcases position with same | defined
    · exact Or.inl same
    · have before := beforeOfDefined b defined
      right
      rw [tableBefore_eq H larger emptyTable a b largerCons,if_pos (order b a before read)]
      exact Option.some_ne_none _

#print axioms ordered
end AspisR1.PFin_CollisionTransport
end
