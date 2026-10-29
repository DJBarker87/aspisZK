import R1Z.PV_RunJoin_NonVacuity61
import R1Z.PV_RunJoin_ResultPost41
import R1Z.PV_RunJoin_MapErrInstalled60
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_CaptureBoundary61
open Aeneas Aeneas.Std Result ProverRwFull
variable [ExternalTypes]

/-- Diagnostic dictionary, not a deployed dictionary or a model witness. -/
@[reducible] def rejecting (ops : ExternalFuns) : ExternalFuns :=
  {ops with op12 := fun _ _ _ => .div}

theorem no_produced (ops : ExternalFuns) :
    letI : ExternalFuns := rejecting ops
    ∀ p, ¬ PV_RunJoin_ActualProvenance60.Produced p := by
  letI : ExternalFuns := rejecting ops
  intro p hp
  obtain ⟨T,store,input,audit,next,h⟩ := hp
  unfold PV_RunJoin_NativeControl55.run at h
  obtain ⟨a,_,h⟩ := PV_RunJoin_ResultPost41.bind_success _ _ _ h
  rcases a with ⟨status,state⟩
  change ((Result.div : Result (core.result.Result _ verifier.Error)) >>= _) = .ok _ at h
  cases h

theorem no_successfulCapture (ops : ExternalFuns) :
    letI : ExternalFuns := rejecting ops
    ¬ PV_RunJoin_NonVacuity61.SuccessfulCapture := by
  letI : ExternalFuns := rejecting ops
  rintro ⟨p⟩
  exact no_produced ops p.val p.property

set_option allowUnsafeReducibility true in
attribute [local irreducible] ProverRwP6BoundaryInstall.selected
attribute [local irreducible] PV_RunJoin_WeightInstalled46.selected PV_B2_F_RawNative.selected PV_B2_F_ResourceFamilies.selected

theorem selected_preserves_rejection (base : ExternalTypes)
    (heap : PV_RunJoin_WeightInstalled46.Heap) (box : PV_RunJoin_WeightInstalled46.Box)
    (ops : @ExternalFuns (PV_RunJoin_WeightInstalled46.types base)) :
    @ExternalFuns.op12 _ (PV_RunJoin_WeightInstalled46.selected base heap box (@rejecting (PV_RunJoin_WeightInstalled46.types base) ops)) =
    @ExternalFuns.op12 _ (@rejecting (PV_RunJoin_WeightInstalled46.types base) ops) := by
  unfold PV_RunJoin_WeightInstalled46.selected
  rw [PV_B2_F_RawNative.preserved_12]
  unfold ProverRwP6BodyCandidate.selected ProverRwP6BoundaryInstall.selected
    ProverRwP6FlatInstall.selected ProverRwP6TransitionInstall.selected
    ProverRwBodyNativeWideInstall.selected
  rfl

#print axioms rejecting
#print axioms no_produced
#print axioms no_successfulCapture
#print axioms selected_preserves_rejection
end R1Z.PV_RunJoin_CaptureBoundary61
