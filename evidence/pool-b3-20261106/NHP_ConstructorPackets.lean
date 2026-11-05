import NHC_ErrorConversion
set_option autoImplicit false
open Aeneas Aeneas.Std Result
namespace NHP_ConstructorPackets
abbrev PoolError := NGK_NFR_CHelper.aspis_pool.error.PoolV1ProgramError
abbrev ProgramError := AdapterRw.solana_program_error.ProgramError
/-- Constructor-coded Result arms under (ak); no Arbitrary Result or output premise. -/
def poolReply (reject : Bool) (error : PoolError) : Result (core.result.Result Unit ProgramError) := do
  if reject then
    let mapped ← NGK_NFR_CHelper.convertPoolError error
    ok (.Err mapped)
  else ok (.Ok ())

theorem exact_arms (reject : Bool) (error : PoolError) :
    poolReply reject error = ok (if reject then
      .Err (.Custom (read_discriminant error)) else .Ok ()) := by
  cases reject <;> simp [poolReply,NHC_ErrorConversion.result]
#print axioms exact_arms

theorem full_error_domain (error : PoolError) :
    poolReply true error = ok (.Err (.Custom (read_discriminant error))) := by
  simpa using exact_arms true error
#print axioms full_error_domain
end NHP_ConstructorPackets
