import R1Z.ProverRwEntropyExhaust64
set_option autoImplicit false
noncomputable section
namespace R1Z.ProverRwEntropyBudget64
open R0Z.FsStatement R0Z.FsAbort R0Z.FsGood R0Z.HvzkV
open ProverCommitPublicNonce40 ProverCommitLedger36 ProverRwEntropyAbort64
open ProverRwEntropyExhaust64
attribute [local irreducible] ProverCommitPublicNonce40.generate ProverCommitPublicNonce40.run
attribute [local irreducible] ProverRwEntropyAbort64.failed ProverRwEntropyAbort64.osBad ProverRwEntropyAbort64.zeroBad
/-- For the very same stateful model law, availability is an explicit
additive term. This theorem retains OS errors instead of conditioning them
away. It does not assert that adaptive native retries use this finite law. -/
theorem failure_bound
    (nonce : Coins → Path) (admitted : ∀ coins, nonce coins ≠ 0)
    (schedule : Coins → Schedule) (initial : Coins → State)
    (cursor : ∀ coins, (initial coins).cursor = 0) :
    eventMass (failed nonce schedule tape initial) ≤
      eventMass (osBad nonce schedule tape initial) + zeroBudget := by
  have hz : eventMass (zeroBad nonce schedule tape initial) ≤ zeroBudget :=
    ProverRwEntropyExhaust64.exhaustion_mass nonce admitted schedule initial cursor
  have hf : eventMass (failed nonce schedule tape initial) =
      eventMass (osBad nonce schedule tape initial) +
      eventMass (zeroBad nonce schedule tape initial) :=
    ProverRwEntropyAbort64.failure_mass nonce schedule tape initial
  calc
    eventMass (failed nonce schedule tape initial) =
        eventMass (osBad nonce schedule tape initial) +
        eventMass (zeroBad nonce schedule tape initial) := hf
    _ ≤ eventMass (osBad nonce schedule tape initial) + zeroBudget :=
      add_le_add (le_refl _) hz


#print axioms failure_bound
end R1Z.ProverRwEntropyBudget64
