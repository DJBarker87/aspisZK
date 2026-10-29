import R1Z.PV_RunJoin_ProducedOrigin61
import R1Z.PV_RunJoin_CircleInstalled52
import R1Z.PV_RunJoin_CircleReach51
import R1Z.PV_RunJoin_LinkR24Discharged54
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_CircleObstruction61
open Aeneas Aeneas.Std Result ProverRwFull PV_RunJoin_WeightInstalled46

@[reducible] def rejecting [ExternalTypes] (ops : ExternalFuns) : ExternalFuns :=
  {ops with op259 := fun _ _ => .div}

/-- Diagnostic counterinstance to universal native nonemptiness over the
currently arbitrary residual dictionary. This is NOT a model witness. -/
theorem no_capture (base : ExternalTypes) (heap : Heap) (box : Box)
    (ops : @ExternalFuns (types base)) :
    letI : ExternalTypes := types base
    letI : ExternalFuns := selected base heap box (@rejecting (types base) ops)
    ¬ PV_RunJoin_NonVacuity61.SuccessfulCapture := by
  letI : ExternalTypes := types base
  letI : ExternalFuns := selected base heap box (@rejecting (types base) ops)
  rintro ⟨p⟩
  obtain ⟨before,middle,z0,z1,f25,f26,h25,_,_⟩ :=
    PV_RunJoin_ProducedOrigin61.circles base heap box (@rejecting (types base) ops) p.val p.property
  obtain ⟨block,_,hblock⟩ := PV_RunJoin_CircleReach51.first _ _ _ _ _ h25
  change @ExternalFuns.op259 _ (selected base heap box (@rejecting (types base) ops)) _ _ = _ at hblock
  rw [PV_RunJoin_CircleInstalled52.installed_projection] at hblock
  cases hblock

theorem not_uniform_capture (base : ExternalTypes) (heap : Heap) (box : Box)
    (ops : @ExternalFuns (types base)) :
    ¬ (∀ candidate : @ExternalFuns (types base),
      @PV_RunJoin_NonVacuity61.SuccessfulCapture (types base) (selected base heap box candidate)) := by
  intro h
  exact no_capture base heap box ops (h (@rejecting (types base) ops))

/-- All nine Links can hold with the actual layout families and no native
capture. This explicitly fails the requested non-degeneracy condition. -/
theorem degenerate_links (base : ExternalTypes) (heap : Heap) (box : Box)
    (ops : @ExternalFuns (types base)) :
    letI : ExternalTypes := types base
    letI : ExternalFuns := selected base heap box (@rejecting (types base) ops)
    PV_RunJoin_PublishProduced60.Links := by
  letI : ExternalTypes := types base
  letI : ExternalFuns := selected base heap box (@rejecting (types base) ops)
  exact PV_RunJoin_NonVacuity61.empty_links (no_capture base heap box ops)
    PV_RunJoin_LinkR24Discharged54.complete

#print axioms rejecting
#print axioms no_capture
#print axioms not_uniform_capture
#print axioms degenerate_links
end R1Z.PV_RunJoin_CircleObstruction61
