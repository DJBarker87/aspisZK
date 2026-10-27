import SCJ_FirstHitWitness
set_option autoImplicit false
noncomputable section
namespace AspisR1.SCJ_BeforeTable
open FS FS2.Duplex AspisV8PairedCommitment
variable {I A : Type} [DecidableEq I]
/-- The exact local table inclusion required by collision transport follows
from preserving the first-occurrence order, not arbitrary occurrence order. -/
theorem extension (H : I → A) (small full : List (I × A))
    (smallCons : ∀ q ∈ small, q.2 = H q.1)
    (fullCons : ∀ q ∈ full, q.2 = H q.1)
    (order : ∀ b a, Read small a → Before small b a → Before full b a)
    (a : I) (read : Read small a) :
    SCJ_TableExtension.Extends (tableBefore emptyTable small a)
      (tableBefore emptyTable full a) := by
  intro b answer value
  rw [tableBefore_eq H small emptyTable a b smallCons] at value
  by_cases prior : Before small b a
  · rw [if_pos prior] at value
    rw [tableBefore_eq H full emptyTable a b fullCons,if_pos (order b a read prior)]
    exact value
  · rw [if_neg prior] at value
    cases value

#print axioms extension
end AspisR1.SCJ_BeforeTable
end
