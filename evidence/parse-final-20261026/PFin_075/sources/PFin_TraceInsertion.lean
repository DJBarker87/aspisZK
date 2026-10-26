import PFin_TraceIndex
set_option autoImplicit false
noncomputable section
namespace AspisR1.PFin_TraceInsertion
open FS FS2 FS2.Duplex AspisV8PairedCommitment PFin_TraceIndex
variable {I A : Type} [DecidableEq I]

theorem read (left middle right : List (I × A)) (a : I) (ha : Read (left++right) a) :
    Read (left++middle++right) a := by
  rcases (read_append _ _ _).mp ha with old | fresh
  · exact (read_append _ _ _).mpr (Or.inl ((read_append _ _ _).mpr (Or.inl old)))
  · exact (read_append _ _ _).mpr (Or.inr fresh)

theorem before (left middle right : List (I × A))
    (disjoint : ∀ x,Read right x → ¬Read middle x) (a b : I)
    (ha : Read (left++right) a) (hb : Read (left++right) b)
    (order : Before (left++right) a b) : Before (left++middle++right) a b := by
  refine ⟨read left middle right a ha,?_⟩
  have old := order.2
  by_cases aL : Read left a
  · by_cases bL : Read left b
    · simpa only [index_append,if_pos aL,if_pos bL] using old
    · have bR := ((read_append _ _ _).mp hb).resolve_left bL
      have bM := disjoint b bR
      have boundA := firstIdx_lt_length a left aL
      simp only [index_append,if_pos aL,if_neg bL,if_neg bM,List.length_append]
      omega
  · have aR := ((read_append _ _ _).mp ha).resolve_left aL
    have aM := disjoint a aR
    by_cases bL : Read left b
    · have boundB := firstIdx_lt_length b left bL
      simp only [index_append,if_neg aL,if_pos bL] at old
      omega
    · have bR := ((read_append _ _ _).mp hb).resolve_left bL
      have bM := disjoint b bR
      simp only [index_append,if_neg aL,if_neg bL] at old
      simp only [index_append,if_neg aL,if_neg bL,if_neg aM,if_neg bM,List.length_append]
      omega

#print axioms read
#print axioms before
end AspisR1.PFin_TraceInsertion
end
