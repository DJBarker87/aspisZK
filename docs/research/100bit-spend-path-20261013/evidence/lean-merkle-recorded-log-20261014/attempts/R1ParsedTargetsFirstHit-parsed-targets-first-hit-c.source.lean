import R1ParsedTargetsCollision

/-! Event containment for a finite family of parsed-state predictors under an
explicit first-read order premise. -/
set_option autoImplicit false
namespace AspisR1.ParsedTargetsFirstHit

open FS FS2 FS2.Duplex
open AspisV8R19.SourceDuplexStep

variable {M Cv : Type} {L : Nat}

theorem first_hit {B : Nat}
    (pred : Fin B → Addr L → Option State) (Qtot : Nat)
    (H : Addr L → State) (tr : List (Addr L × State))
    (hcons : ∀ q ∈ tr, q.2 = H q.1)
    (hQ : firstReads emptyTable tr ≤ Qtot)
    (a b : Addr L) (ha : Read tr a)
    (hb : b = a ∨ Before tr b a)
    (j : Fin B) (hp : pred j b = some (H a)) :
    hitsBad (ParsedTargetsCollision.bad pred Qtot) emptyTable tr := by
  apply FS.hitsBad_of_first (ParsedTargetsCollision.bad pred Qtot)
    H a tr emptyTable hcons ha rfl
  refine ⟨j, ?_⟩
  refine ⟨card_dom_lt H tr a hcons ha Qtot hQ, b, ?_, hp⟩
  rcases hb with heq | hbefore
  · exact Or.inl heq
  · right
    rw [tableBefore_eq H tr emptyTable a b hcons, if_pos hbefore]
    exact Option.some_ne_none _

#print axioms first_hit

end AspisR1.ParsedTargetsFirstHit
