import RPz7_PhaseIso
set_option autoImplicit false
namespace NDO_PhaseIdentity

/-- The historical S1SemanticPhaseV1 abbreviation and replay abbreviation
retain this exact FirstCaller carrier. This does not identify the emitted
producer's distinct verifier.Phase. -/
theorem retainedCarrier :
    RPz7_PhaseIso.Phase = AspisR1PublicPreparation.FirstCaller.Phase := rfl
#print axioms retainedCarrier

/-- Reuse the existing all-callback round trip, retaining explicit transport. -/
theorem observerRoundtrip {R : Type}
    (obs : Option (RPz7_PhaseIso.Phase → R)) :
    RPz7_PhaseIso.observerToFirst (RPz7_PhaseIso.observerToVerifier obs) = obs :=
  RPz7_PhaseIso.observer_first_roundtrip_RPz7 obs
#print axioms observerRoundtrip

theorem noneToFirst {R : Type} :
    RPz7_PhaseIso.observerToFirst (R := R) none = none := rfl
#print axioms noneToFirst
end NDO_PhaseIdentity
