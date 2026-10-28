import NCA_SemanticFrames
set_option autoImplicit false
namespace AspisR1.NCH_WindowLift

/-- Meaning of a verified native modifies region on fixed, successive states.
This is a per-call observation, not a freely selected final carrier. -/
def WritesOnly {α : Type} (before after : Nat → α) (start count : Nat) : Prop :=
  ∀ k, k < start ∨ start + count ≤ k → after k = before k

/-- The two actual calls share the intermediate state. Their verified regions
may overlap; only their upper bounds matter for the exterior suffix. -/
theorem compose_suffix {α : Type} (before middle after : Nat → α)
    (a n b m boundary : Nat)
    (first : WritesOnly before middle a n)
    (second : WritesOnly middle after b m)
    (firstBound : a+n≤boundary) (secondBound : b+m≤boundary) :
    ∀ k, boundary≤k → after k=before k := by
  intro k suffix
  exact (second k (Or.inr (by omega))).trans (first k (Or.inr (by omega)))

/-- Source row geometry supplies the actual header and payload domains,
including empty ordinary payloads. No whole-buffer normalization is used. -/
theorem row_suffix {α : Type} (before middle after : Nat → α)
    (row : Nat) (bound : row<27)
    (header : WritesOnly before middle (JFw_Geometry.destPos row) 5)
    (payload : WritesOnly middle after (JFw_Geometry.destPos row+5)
      (OraclePortCompactDraft.rowShape row).2) :
    ∀ k, 13831≤k → after k=before k := by
  obtain ⟨_,_,_,next,_,endBound⟩ := JFw_Geometry.step row bound
  apply compose_suffix before middle after
    (JFw_Geometry.destPos row) 5 (JFw_Geometry.destPos row+5)
    (OraclePortCompactDraft.rowShape row).2 13831 header payload <;> omega

#print axioms compose_suffix
#print axioms row_suffix
end AspisR1.NCH_WindowLift
