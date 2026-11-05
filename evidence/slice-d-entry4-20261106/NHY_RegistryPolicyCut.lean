import NHJ_RegistryHeader
set_option autoImplicit false
noncomputable section
namespace NHY_RegistryPolicyCut
open Aeneas Aeneas.Std Result
open NHJ_RegistryHeader
/-- The first missing callee boundary after the five CLOSED header guards.
It is explicitly a child law, not a successful-authentication hypothesis.
No decoder/PDA suffix is reached on this full Result error arm. -/
theorem policy_error {E : Type} (missing : AspisR1.IDa_Deployed.Uninstalled E)
    (devnet : Bool) (indexError : E) (reservation : AspisR1.NP6_StdModel.Reservation)
    (verifier pool : Key) (account registry entry : Account) (master : Master) (slot : U64)
    (good : ¬ Bad devnet pool master)
    (error : AdapterRw.aspis_statement.pool_v1.format.PoolV1FormatError)
    (child : (configuration missing devnet indexError reservation).adapter.op15 master.verifier_policy = ok (.Err error)) :
    AdapterRw.r1_pool_adapter.owned.authenticate_invariant_release_registry
      (configuration missing devnet indexError reservation).adapter verifier pool account master registry entry slot =
      ok (.Err AdapterRw.solana_program_error.ProgramError.InvalidAccountData) := by
  classical
  simp only [Bad,not_or,not_not] at good
  rcases good with ⟨g0,g1,g2,g3,g4⟩
  let ops := (configuration missing devnet indexError reservation).adapter
  have key : ops.op39 pool = ok pool := rfl
  have mask : ops.op13 = ok 1#u8 := rfl
  have poolId : ops.op45 = ok (NHJ_IdPacket.pool devnet) := rfl
  have registryId : ops.op46 = ok (NHJ_IdPacket.registry devnet) := rfl
  change AdapterRw.r1_pool_adapter.owned.authenticate_invariant_release_registry ops _ _ _ _ _ _ _ = _
  have policy : ops.op15 master.verifier_policy = ok (.Err error) := child
  unfold AdapterRw.r1_pool_adapter.owned.authenticate_invariant_release_registry
  simp only [key,poolId,registryId,mask,NGL_ArrayEquality.ne_value,bind_tc_ok,lift]
  simp only [g0,g1,g2,g3,g4,decide_true,Bool.not_true,Bool.false_eq_true,if_false,policy,bind_tc_ok]
  simp [AdapterRw.core.result.Result.map_err,
    AdapterRw.r1_pool_adapter.owned.authenticate_invariant_release_registry.closure.Insts.CoreOpsFunctionFnOnceTuplePoolV1FormatErrorProgramError,
    core.result.Result.Insts.CoreOpsTry.branch,
    core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,
    core.convert.FromSame]
  rfl
#print axioms policy_error
end NHY_RegistryPolicyCut
