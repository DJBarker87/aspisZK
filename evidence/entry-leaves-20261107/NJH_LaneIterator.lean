import NJD_LaneStep
set_option autoImplicit false
noncomputable section
namespace NJH_LaneIterator
open Aeneas Aeneas.Std Result
abbrev Frontier := Fin 20 → NJD_LaneStep.Node
/-- NJH_lane.rs.txt: `frontier[other][word].0 == expected`, for arbitrary
other<20 and word<8, where expected is decoded[word] iff canonical &&
other==level, else the pre-coordinate. This is ONLY iterator/assignment/frame;
no parent Result, decoder value, successful continuation or op50 equality. -/
def cut (before after : Frontier) (level : Fin 20) (canonical : Bool)
    (decoded : NJD_LaneStep.Node) : Prop :=
  ∀ other word, after other word =
    if canonical = true ∧ other = level then decoded word else before other word

theorem success (before after : Frontier) (level : Fin 20)
    (decoded : NJD_LaneStep.Node) (h : cut before after level true decoded) :
    after = NJD_LaneStep.write before level decoded := by
  funext other word
  simpa only [NJD_LaneStep.write, true_and, ite_apply] using h other word

theorem error (before after : Frontier) (level : Fin 20)
    (decoded : NJD_LaneStep.Node) (h : cut before after level false decoded) :
    after = before := by
  funext other word
  simpa only [Bool.false_eq_true, false_and, if_false] using h other word

theorem selected (before after : Frontier) (level : Fin 20)
    (decoded : NJD_LaneStep.Node) (h : cut before after level true decoded) :
    after level = decoded := by
  rw [success before after level decoded h]
  exact NJD_LaneStep.written before level decoded

theorem outside (before after : Frontier) (level other : Fin 20)
    (canonical : Bool) (decoded : NJD_LaneStep.Node)
    (h : cut before after level canonical decoded) (different : other ≠ level) :
    after other = before other := by
  funext word
  simpa only [different, and_false, if_false] using h other word
#print axioms success
#print axioms error
#print axioms selected
#print axioms outside
end NJH_LaneIterator
