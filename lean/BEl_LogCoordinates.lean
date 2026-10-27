import BEl_Recorder
set_option autoImplicit false
noncomputable section
namespace AspisR1.BEl_LogCoordinates
open Aeneas Aeneas.Std Result SdkC_Source

/-- Occurrence-indexed projections distinguish duplicates and ordering. -/
def coordinate (log : Log) (index : Nat) : Option Query := log[index]?

/-- Universal coordinate equality is full log equality, not merely a count. -/
theorem ext (left right : Log) (same : ∀ index, coordinate left index = coordinate right index) :
    left = right := by
  apply List.ext_getElem?
  exact same

/-- A single observed coordinate is weaker; universal quantification is required. -/
theorem prepend (before left right : Log)
    (same : ∀ index, coordinate left index = coordinate right index) :
    before ++ left = before ++ right := by
  rw [ext left right same]

/-- The chronological cut retains exactly the universally identified suffix. -/
theorem cut (before left right : Log)
    (same : ∀ index, coordinate left index = coordinate right index) :
    BEi_RecorderCut.issued before (before ++ left) = right := by
  simp only [BEi_RecorderCut.issued,List.drop_left]
  exact ext left right same

#print axioms ext
#print axioms prepend
#print axioms cut
end AspisR1.BEl_LogCoordinates
end
