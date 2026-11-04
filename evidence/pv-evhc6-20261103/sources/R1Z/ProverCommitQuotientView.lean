import R1Z.ProverCommitTapeMeasure

/-! A quotient endpoint for the actual joint honest view. This covers all
payload cells, not just H1 or one trace coordinate. Commitment source reads
are still a separate identification obligation. -/
set_option autoImplicit false
noncomputable section
namespace R1Z.ProverCommitTapeCompletion
open R0P R0Z.JointView R0Z.MaskLayout R0Z.FsAbortBounds
attribute [local instance] Classical.propDecidable
variable {K CommitHandle Aux Bat : Type} [Field K] [Fintype K] [DecidableEq K]
  [Algebra (ZMod AspisCircleGroupOrder.P) K] {F : Subfield K}
  [R0Z.HonestView.BatchedLayer K Bat]

theorem payload_completion (h : HonestProver K) (B : PackBasis F)
    (x : Statement K CommitHandle) (w : HonestInstance h) (ch : Challenges K)
    (t : Tape K F) (pad : Padding K F) :
    payload (Bat := Bat) h B x w ch (complete (project t) pad) =
      payload h B x w ch t := by
  unfold payload R0Z.HonestView.run
  rw [applyAff_completion]
  rfl

theorem view_completion (h : HonestProver K) (B : PackBasis F)
    (outputs : Statement K CommitHandle → Challenges K → Aux)
    (x : Statement K CommitHandle) (w : HonestInstance h) (ch : Challenges K)
    (t : Tape K F) (pad : Padding K F) :
    view (Bat := Bat) h B outputs x w ch (complete (project t) pad) =
      view h B outputs x w ch t := by
  unfold view
  rw [payload_completion]

/-- The entire existing honest view has its exact model law when sampled on
uniform quotient tapes with any chosen ignored-coordinate representative. -/
theorem quotient_view_mass (h : HonestProver K) (B : PackBasis F)
    (outputs : Statement K CommitHandle → Challenges K → Aux)
    (x : Statement K CommitHandle) (w : HonestInstance h) (ch : Challenges K)
    (choose : SourceTape K F → Padding K F)
    (event : View K CommitHandle Aux Bat → Prop) :
    mass (fun s : SourceTape K F => event (view h B outputs x w ch (complete s (choose s)))) =
      mass (fun t : Tape K F => event (view h B outputs x w ch t)) :=
  observable_mass (view h B outputs x w ch) (view_completion h B outputs x w ch) choose event

#print axioms payload_completion
#print axioms view_completion
#print axioms quotient_view_mass
end R1Z.ProverCommitTapeCompletion
