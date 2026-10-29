import R1Z.PV_RunJoin_PublishProduced60
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_NonVacuity61
open ProverRwFull
variable [ExternalTypes] [ExternalFuns]

/-- A successful native capture exists. This is a separate obligation from Links. -/
def SuccessfulCapture : Prop := Nonempty PV_RunJoin_ActualProvenance60.ActualPhase

theorem successfulCapture_iff : SuccessfulCapture ↔
    ∃ p, PV_RunJoin_ActualProvenance60.Produced p := by
  constructor
  · rintro ⟨p⟩
    exact ⟨p.val,p.property⟩
  · rintro ⟨p,hp⟩
    exact ⟨⟨p,hp⟩⟩

/-- Every phase-indexed link degenerates when capture has no successful input.
The remaining global R24 law is deliberately retained. -/
theorem empty_links (empty : ¬ SuccessfulCapture)
    (r24 : PV_RunJoin_PublishProduced60.PV_RunJoin_Link_R24Sampler) :
    PV_RunJoin_PublishProduced60.Links := by
  have absent (p : PV_RunJoin_ActualProvenance60.ActualPhase) : False := empty ⟨p⟩
  refine ⟨r24, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro _ p; exact (absent p).elim
  · intro p; exact (absent p).elim
  · intro p; exact (absent p).elim
  · intro p; exact (absent p).elim
  · intro p; exact (absent p).elim
  · intro p; exact (absent p).elim
  · intro p; exact (absent p).elim
  · intro _ _ p; exact (absent p).elim

#print axioms SuccessfulCapture
#print axioms successfulCapture_iff
#print axioms empty_links
end R1Z.PV_RunJoin_NonVacuity61
