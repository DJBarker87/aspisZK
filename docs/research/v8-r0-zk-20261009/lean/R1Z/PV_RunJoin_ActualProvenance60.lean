import R1Z.PV_RunJoin_ActualRun59
import R1Z.PV_RunJoin_NativePublication55
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_ActualProvenance60
open Aeneas Aeneas.Std Result ProverRwFull
open PV_RunJoin_NativeControl55 (Phase)
variable [ExternalTypes] [ExternalFuns]

/-- Capture the source callback argument. This callback adds no validation,
serializer equality, challenge property, or assumed backend association. -/
def capture (p : Phase) : Result (core.result.Result Phase verifier.Error) := ok (.Ok p)

/-- Exact successful native prefix up to publication. The callback is merely
an instrument returning its argument; no publication success is required. -/
def Produced (p : Phase) : Prop :=
  ∃ (T : Type) (store : aspis_prover.state_only_hiding.StateOnlyMaskNonceStore T)
    (input : PV_RunJoin_NativePublication55.Input T)
    (audit : prover.MaskedFixtureAudit) (next : T),
    PV_RunJoin_NativeControl55.run capture store input.public1 input.compiled .S2 input.hash
      input.context input.binding input.attempt input.store=ok (.Ok (p,audit),next)

abbrev ActualPhase := {p : Phase // Produced p}

def runs (p : ActualPhase) : PV_RunJoin_PublishSkeleton54.Run := PV_RunJoin_ActualRun.runs p.val

theorem families (p : ActualPhase) :
    (runs p).data=PV_RunJoin_ActualRun.data p.val ∧
    (runs p).plan=PV_RunJoin_ActualRun.plans p.val := ⟨rfl,rfl⟩

theorem layout (p : ActualPhase) :
    (runs p).plan.queries.length=22 ∧ (runs p).plan.slots.length=6 ∧
    (runs p).plan.offOpenings=10055 ∧ (runs p).plan.offNodes=28359 ∧
    (runs p).plan.proofBytes=57607 := PV_RunJoin_ActualRun.layout p.val

#print axioms capture
#print axioms Produced
#print axioms runs
#print axioms families
#print axioms layout
end R1Z.PV_RunJoin_ActualProvenance60
