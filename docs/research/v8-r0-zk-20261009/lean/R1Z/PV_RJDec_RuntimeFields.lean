import R1Z.PV_RunJoin_Deployed
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RJDec_RuntimeFields
open Aeneas Aeneas.Std R0Z R0Z.JointView R0Z.FsStatement R1Z.GamesR1 R1Z.Batched
local notation "K" => PrivacyR1AcctBasis.K
variable [ProverRwFull.ExternalTypes]
local instance : ProverRwRngCaller.NativeTypes := PV_RunJoin_CallerWorld.nativeTypes
local instance : ProverRwRngCaller.ErasureFns := ⟨fun _ v => .ok v, fun _ v => .ok v⟩
variable {CH Aux Coins N L C : Type}
variable (r : PV_RunJoin_Deployed.Runtime CH Aux Coins N L C)

/-- Changing either observation field does not select a different source body.
This is an interface fact, not an installation or a native counterexample. -/
theorem execute_independent
    (disclosed : R1Adv K CH Aux → Statement K CH →
      Result (PV_RunJoin_Deployed.Output N L C) → View K CH Aux R1Bat)
    (oracle : R1Adv K CH Aux → Statement K CH →
      Result (PV_RunJoin_Deployed.Output N L C) → List (Bytes × OracleAnswer))
    (h : R0Z.ZkStatement.HonestProver K) (x : Statement K CH) (w : h.Instance)
    (coin : PV_RunJoin_Deployed.World r) :
    PV_RunJoin_Deployed.execute {r with disclosed := disclosed, observerOracle := oracle}
      h x w coin = PV_RunJoin_Deployed.execute r h x w coin := rfl

/-- Even the complete execution function does not determine the oracle field.
The two updates are examples of DATA, not proposed native observations. -/
theorem oracle_underdetermined (event : Bytes × OracleAnswer)
    (adv : R1Adv K CH Aux) (x : Statement K CH)
    (out : Result (PV_RunJoin_Deployed.Output N L C)) :
    ({r with observerOracle := fun _ _ _ => []}).observerOracle adv x out ≠
    ({r with observerOracle := fun _ _ _ => [event]}).observerOracle adv x out := by
  intro same
  have lengths := congrArg List.length same
  exact (by decide : (0 : Nat) ≠ 1) lengths
#print axioms execute_independent
#print axioms oracle_underdetermined
end R1Z.PV_RJDec_RuntimeFields
