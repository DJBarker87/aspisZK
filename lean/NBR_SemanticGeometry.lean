import JFw_Geometry
set_option autoImplicit false
namespace AspisR1.NBR_SemanticGeometry
open OraclePortCompactDraft

/-- Associate the natural-number offsets used by the native K002 gate with
the existing symbolic geometry used by semantic-expansion induction. -/
theorem source (row : Nat) (bound : row<27) :
    JFw_Geometry.sourcePos (row+1)=JFw_Geometry.sourcePos row+5+
      (if 14≤row then (rowShape row).2/2 else (rowShape row).2) ∧
    JFw_Geometry.destPos (row+1)=JFw_Geometry.destPos row+5+(rowShape row).2 ∧
    JFw_Geometry.sourcePos (row+1)≤7015 ∧
    JFw_Geometry.destPos (row+1)≤13831 := by
  obtain ⟨_,_,source,dest,ib,ob⟩ := JFw_Geometry.step row bound
  exact ⟨source,dest,ib,ob⟩

#print axioms source
end AspisR1.NBR_SemanticGeometry
