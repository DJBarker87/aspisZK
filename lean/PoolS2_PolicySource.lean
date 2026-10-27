import Hist_Authority
set_option autoImplicit false
noncomputable section
namespace AspisR1.PoolS2_PolicySource
open Aeneas Aeneas.Std Result
abbrev Policy := AdapterRw.aspis_statement.pool_v1.format.VerifierPolicyV1
abbrev FormatError := AdapterRw.aspis_statement.pool_v1.format.PoolV1FormatError
/-- Actual AENEAS010 body; canonical existing carriers, literal source flags,
and total full-byte equality. No external template or SDK child. -/
def pool_v1.format.validate_verifier_policy_v1
  (policy : Policy) :
  Result (core.result.Result Unit FormatError)
  := do
  let i ← (ok 3#u8)
  let i1 ← lift (~~~ i)
  let i2 ← lift (policy.flags &&& i1)
  if i2 != 0#u8
  then
    ok (core.result.Result.Err
      AdapterRw.aspis_statement.pool_v1.format.PoolV1FormatError.UnsupportedFlags)
  else
    let a := Array.repeat 32#usize 0#u8
    let b ←
      Hist_Authority.keyEq
        policy.registry_program a
    if b
    then
      ok (core.result.Result.Err
        AdapterRw.aspis_statement.pool_v1.format.PoolV1FormatError.ZeroRequiredBinding)
    else
      let a1 := Array.repeat 32#usize 0#u8
      let b1 ←
        Hist_Authority.keyEq
          policy.policy_binding a1
      if b1
      then
        ok (core.result.Result.Err
          AdapterRw.aspis_statement.pool_v1.format.PoolV1FormatError.ZeroRequiredBinding)
      else
        let i3 ←
          (ok 1#u8)
        let i4 ← lift (policy.flags &&& i3)
        let i5 ←
          (ok 2#u8)
        let i6 ← lift (policy.flags &&& i5)
        if i6 != 0#u8
        then
          if i4 != 0#u8
          then
            let a2 := Array.repeat 32#usize 0#u8
            let b2 ←
              Hist_Authority.keyEq
                policy.registry_authority a2
            if true != b2
            then
              ok (core.result.Result.Err
                AdapterRw.aspis_statement.pool_v1.format.PoolV1FormatError.InvalidAuthorityMode)
            else ok (core.result.Result.Ok ())
          else
            ok (core.result.Result.Err
              AdapterRw.aspis_statement.pool_v1.format.PoolV1FormatError.InvalidAuthorityMode)
        else
          let a2 := Array.repeat 32#usize 0#u8
          let b2 ←
            Hist_Authority.keyEq
              policy.registry_authority a2
          if (i4 != 0#u8) != b2
          then
            ok (core.result.Result.Err
              AdapterRw.aspis_statement.pool_v1.format.PoolV1FormatError.InvalidAuthorityMode)
          else ok (core.result.Result.Ok ())


#print axioms pool_v1.format.validate_verifier_policy_v1
end AspisR1.PoolS2_PolicySource
end
