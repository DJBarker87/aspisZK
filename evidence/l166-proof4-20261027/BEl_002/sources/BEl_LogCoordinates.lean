import BEl_Recorder
set_option autoImplicit false
noncomputable section
namespace AspisR1.BEl_LogCoordinates
open Aeneas Aeneas.Std Result SdkC_Source

/-- Occurrence-indexed projections distinguish duplicates and ordering. -/
def at (log : Log) (index : Nat) : Option Query := log[index]?

/-- Universal coordinate equality is full log equality, not merely a count. -/
theorem ext (left right : Log) (same : ∀ index, at left index = at right index) :
    left = right := by
  apply List.ext_getElem?
  exact same

/-- A single observed coordinate is weaker; universal quantification is required. -/
theorem prefix (before left right : Log)
    (same : ∀ index, at left index = at right index) :
    before ++ left = before ++ right := by
  rw [ext left right same]

/-- The chronological cut retains exactly the universally identified suffix. -/
theorem cut (before left right : Log)
    (same : ∀ index, at left index = at right index) :
    BEi_RecorderCut.issued before (before ++ left) = right := by
  simp only [BEi_RecorderCut.issued,List.drop_left]
  exact ext left right same

#print axioms ext
#print axioms prefix
#print axioms cut
end AspisR1.BEl_LogCoordinates
end
