import R1Z.PV_RunJoin_TrustItems
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_TrustBoundary
variable {E File Reply Time Worker Context Coins Rest Payload : Type} [Fintype Rest]
variable (d : Data E File Reply Time Worker Context Coins Rest Payload)
variable (T : PV_RunJoin_TrustItems d)
include T

theorem initial_projection (c : Coins) :
    (d.nativeObservation c).initial = (d.extractedObservation c).initial :=
  congrArg Observation.initial (T.observation c)

theorem calls_projection (c : Coins) :
    (d.nativeObservation c).calls = (d.extractedObservation c).calls :=
  congrArg Observation.calls (T.observation c)

theorem final_projection (c : Coins) :
    (d.nativeObservation c).final = (d.extractedObservation c).final :=
  congrArg Observation.final (T.observation c)

theorem filesystem_projection (c : Coins) :
    (d.nativeObservation c).filesystem = (d.extractedObservation c).filesystem :=
  congrArg Observation.filesystem (T.observation c)

theorem payload_projection (c : Coins) :
    (d.nativeObservation c).payload = (d.extractedObservation c).payload :=
  congrArg Observation.payload (T.observation c)

/-- Exact events, their order, pre-call worlds, replies, and next worlds are
retained. Entropy/file/time/worker projections are consequences of ONE joint
equality, not additional trust assumptions about isolated marginal traces. -/
theorem event_projection {A : Type}
    (project : PV_RunJoin_OsWorld.World E File Reply Time Worker ×
      Call E File Reply Time Worker → A) (c : Coins) :
    (d.nativeObservation c).calls.map project =
      (d.extractedObservation c).calls.map project :=
  congrArg (List.map project) (calls_projection d T c)

#print axioms initial_projection
#print axioms calls_projection
#print axioms final_projection
#print axioms filesystem_projection
#print axioms payload_projection
#print axioms event_projection
end R1Z.PV_RunJoin_TrustBoundary
