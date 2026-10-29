import R1Z.PV_RunJoin_ActualProvenance60
import R1Z.PV_RunJoin_NativeVariantTransport55
set_option autoImplicit false
namespace R1Z.PV_RunJoin_ProducedVariant60
open Aeneas Aeneas.Std Result ProverRwFull
open PV_RunJoin_ResultRelation55
open PV_RunJoin_ActualProvenance60 (capture Produced)
variable [ExternalTypes] [ExternalFuns]

theorem actual (p : PV_RunJoin_NativeControl55.Phase) (produced : Produced p) : p.variant=.S2 := by
  obtain ⟨T,store,input,audit,next,hp⟩ := produced
  have h := PV_RunJoin_NativeVariantTransport55.complete
    (fun (p q : PV_RunJoin_NativeControl55.Phase) => p.variant=transport.Variant.S2)
    capture capture store input.public1 input.compiled .S2
    (fun phase hv => Rel.ok (CoreRel.ok hv))
    input.hash input.context input.binding input.attempt input.store
  rw [hp] at h
  cases h with
  | ok h =>
    rcases h with ⟨hc,_⟩
    cases hc with
    | ok h => exact h.1

#print axioms actual
end R1Z.PV_RunJoin_ProducedVariant60
