import ProverPin2.Funs
open Aeneas Aeneas.Std Result ControlFlow Error
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000
set_option maxRecDepth 2048

namespace ProverPin2
namespace RW
noncomputable section

-- type of the emission that package g2 does not declare, block sha256 d54ceb6be81173d638cb8460f05a45e47dbdef9c62296a191951b9b71e690e04
def RealR1_client.AttemptSecretsProviderProofAccountNonces.attempt_secrets.closure
  :=
Unit

-- type of the emission that package g2 does not declare, block sha256 8e300660224bf3178210b03e64f88ed1f169b8838c95e74d81fd1fee13538ecc
structure RealR1_client.ProofAccountNonces where
  nonces : Array (Array Std.U8 32#usize) 8#usize

-- block emitted by tool k2 (7271db7e), sha256 004286d3054727b95d534b6384fcb7ce58bdb2b169e0cd0d502f488269622776, source ['/home/dombarker/project-offloads/codex-pv-aspis-rewrite-20261111/src-rw/crates/aspis-prover/src/state_only_entropy.rs', 312, 329]
def
  aspis_prover.state_only_entropy.StateOnlyAttemptSecrets.generate_for_mask_nonce_loop.body
  (mask_nonce : Array Std.U8 32#usize) (iter : core.ops.range.Range Std.Usize)
  :
  Result (ControlFlow (core.ops.range.Range Std.Usize) (core.result.Result
    aspis_prover.state_only_entropy.StateOnlyAttemptSecrets
    aspis_prover.state_only_entropy.StateOnlyAttemptEntropyError))
  := do
  let (o, iter1) ←
    core.iter.range.IteratorRange.next core.iter.range.StepUsize iter
  match o with
  | none =>
    ok (done (core.result.Result.Err
      aspis_prover.state_only_entropy.StateOnlyAttemptEntropyError.RepeatedZeroBlock))
  | some _ =>
    let a := Array.repeat 64#usize 0#u8
    let bytes ←
      zeroize.Zeroizing.new (Array.Insts.ZeroizeZeroize 64#usize
        (zeroize.Zeroize.Blanket U8.Insts.ZeroizeDefaultIsZeroes)) a
    let (s, as_mut_back) ←
      zeroize.Zeroizing.Insts.CoreConvertAsMut.as_mut
        (Array.Insts.CoreConvertAsMutSlice Std.U8 64#usize)
        (Array.Insts.ZeroizeZeroize 64#usize (zeroize.Zeroize.Blanket
        U8.Insts.ZeroizeDefaultIsZeroes)) bytes
    let (r, s1) ← getrandom_1.fill s
    let cf ← core.result.Result.Insts.CoreOpsTry.branch r
    match cf with
    | core.ops.control_flow.ControlFlow.Continue _ =>
      let a1 := Array.repeat 32#usize 0#u8
      let field_mask_entropy ←
        zeroize.Zeroizing.new (Array.Insts.ZeroizeZeroize 32#usize
          (zeroize.Zeroize.Blanket U8.Insts.ZeroizeDefaultIsZeroes)) a1
      let a2 := Array.repeat 32#usize 0#u8
      let leaf_salt_seed ←
        zeroize.Zeroizing.new (Array.Insts.ZeroizeZeroize 32#usize
          (zeroize.Zeroize.Blanket U8.Insts.ZeroizeDefaultIsZeroes)) a2
      let (a3, deref_mut_back) ←
        zeroize.Zeroizing.Insts.CoreOpsDerefDerefMut.deref_mut
          (Array.Insts.ZeroizeZeroize 32#usize (zeroize.Zeroize.Blanket
          U8.Insts.ZeroizeDefaultIsZeroes)) field_mask_entropy
      let (s2, to_slice_mut_back) ← lift (Array.to_slice_mut a3)
      let bytes1 := as_mut_back s1
      let a4 ←
        zeroize.Zeroizing.Insts.CoreOpsDerefDeref.deref
          (Array.Insts.ZeroizeZeroize 64#usize (zeroize.Zeroize.Blanket
          U8.Insts.ZeroizeDefaultIsZeroes)) bytes1
      let s3 ←
        core.array.Array.index (core.ops.index.IndexSlice
          (core.slice.index.SliceIndexRangeToUsizeSlice Std.U8)) a4
          { «end» := 32#usize }
      let s4 ← core.slice.Slice.copy_from_slice core.marker.CopyU8 s2 s3
      let (a5, deref_mut_back1) ←
        zeroize.Zeroizing.Insts.CoreOpsDerefDerefMut.deref_mut
          (Array.Insts.ZeroizeZeroize 32#usize (zeroize.Zeroize.Blanket
          U8.Insts.ZeroizeDefaultIsZeroes)) leaf_salt_seed
      let (s5, to_slice_mut_back1) ← lift (Array.to_slice_mut a5)
      let s6 ←
        core.array.Array.index (core.ops.index.IndexSlice
          (core.slice.index.SliceIndexRangeFromUsizeSlice Std.U8)) a4
          { start := 32#usize }
      let s7 ← core.slice.Slice.copy_from_slice core.marker.CopyU8 s5 s6
      let a6 := to_slice_mut_back s4
      let field_mask_entropy1 := deref_mut_back a6
      let a7 ←
        zeroize.Zeroizing.Insts.CoreOpsDerefDeref.deref
          (Array.Insts.ZeroizeZeroize 32#usize (zeroize.Zeroize.Blanket
          U8.Insts.ZeroizeDefaultIsZeroes)) field_mask_entropy1
      let a8 := Array.repeat 32#usize 0#u8
      let b ←
        core.array.equality.PartialEqArray.ne core.cmp.PartialEqU8 a7 a8
      if b
      then
        let a9 := to_slice_mut_back1 s7
        let leaf_salt_seed1 := deref_mut_back1 a9
        let a10 ←
          zeroize.Zeroizing.Insts.CoreOpsDerefDeref.deref
            (Array.Insts.ZeroizeZeroize 32#usize (zeroize.Zeroize.Blanket
            U8.Insts.ZeroizeDefaultIsZeroes)) leaf_salt_seed1
        let a11 := Array.repeat 32#usize 0#u8
        let b1 ←
          core.array.equality.PartialEqArray.ne core.cmp.PartialEqU8 a10 a11
        if b1
        then
          ok (done (core.result.Result.Ok
            {
              mask_nonce,
              field_mask_entropy := field_mask_entropy1,
              leaf_salt_seed := leaf_salt_seed1
            }))
        else ok (cont iter1)
      else ok (cont iter1)
    | core.ops.control_flow.ControlFlow.Break residual =>
      let r1 ←
        core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
          aspis_prover.state_only_entropy.StateOnlyAttemptSecrets
          aspis_prover.state_only_entropy.StateOnlyAttemptEntropyError.Insts.CoreConvertFromError
          residual
      ok (done r1)

-- block emitted by tool k2 (7271db7e), sha256 006a0249a6b93a818ee476b57fdd2b94f4108b004e470d9534aedb80c443a1e5, source ['/home/dombarker/project-offloads/codex-pv-aspis-rewrite-20261111/src-rw/crates/aspis-prover/src/state_only_entropy.rs', 312, 329]
def
  aspis_prover.state_only_entropy.StateOnlyAttemptSecrets.generate_for_mask_nonce_loop
  (iter : core.ops.range.Range Std.Usize) (mask_nonce : Array Std.U8 32#usize)
  :
  Result (core.result.Result
    aspis_prover.state_only_entropy.StateOnlyAttemptSecrets
    aspis_prover.state_only_entropy.StateOnlyAttemptEntropyError)
  := do
  loop
    (fun iter1 =>
      aspis_prover.state_only_entropy.StateOnlyAttemptSecrets.generate_for_mask_nonce_loop.body
      mask_nonce iter1)
    iter

-- block emitted by tool k2 (7271db7e), sha256 3f9b18a5eb80b39ddd2b9e24437e344eac80caee4c01eaae77e5325d9c4e1f7b, source ['/home/dombarker/project-offloads/codex-pv-aspis-rewrite-20261111/src-rw/crates/aspis-prover/src/state_only_entropy.rs', 306, 308]
def
  aspis_prover.state_only_entropy.StateOnlyAttemptSecrets.generate_for_mask_nonce
  (mask_nonce : Array Std.U8 32#usize) :
  Result (core.result.Result
    aspis_prover.state_only_entropy.StateOnlyAttemptSecrets
    aspis_prover.state_only_entropy.StateOnlyAttemptEntropyError)
  := do
  let a := Array.repeat 32#usize 0#u8
  let b ←
    core.array.equality.PartialEqArray.eq core.cmp.PartialEqU8 mask_nonce a
  if b
  then
    ok (core.result.Result.Err
      aspis_prover.state_only_entropy.StateOnlyAttemptEntropyError.RepeatedZeroBlock)
  else
    aspis_prover.state_only_entropy.StateOnlyAttemptSecrets.generate_for_mask_nonce_loop
      {
        start := 0#usize,
        «end» := aspis_prover.state_only_entropy.ENTROPY_RETRY_LIMIT
      } mask_nonce

-- block emitted by tool k2 (7271db7e), sha256 402325ea1ac30213ca910415ee7d5f6b8d5e6376f97075787e3051bde68e4d66, source ['src/RealR1_client.rs', 79, 79]
def
  RealR1_client.AttemptSecretsProviderProofAccountNonces.attempt_secrets.closure.Insts.CoreOpsFunctionFnOnceTupleStateOnlyAttemptEntropyErrorError.call_once
  (c :
  RealR1_client.AttemptSecretsProviderProofAccountNonces.attempt_secrets.closure)
  (tupled_args : aspis_prover.state_only_entropy.StateOnlyAttemptEntropyError)
  :
  Result verifier.Error
  := do
  ok verifier.Error.Entropy

-- block emitted by tool k2 (7271db7e), sha256 6120c8969c1155bb5a08d12a82a64137697fb1b4193f648db3b337376d48798d, source ['src/RealR1_client.rs', 79, 79]
def
  RealR1_client.AttemptSecretsProviderProofAccountNonces.attempt_secrets.closure.Insts.CoreOpsFunctionFnOnceTupleStateOnlyAttemptEntropyErrorError
  : core.ops.function.FnOnce
  RealR1_client.AttemptSecretsProviderProofAccountNonces.attempt_secrets.closure
  aspis_prover.state_only_entropy.StateOnlyAttemptEntropyError verifier.Error
  := {
  call_once :=
    RealR1_client.AttemptSecretsProviderProofAccountNonces.attempt_secrets.closure.Insts.CoreOpsFunctionFnOnceTupleStateOnlyAttemptEntropyErrorError.call_once
}

-- block emitted by tool k2 (7271db7e), sha256 b3c0ec18a68e04aef474a36269f2d329abbaad95cf304ce66375f6210b199f92, source ['src/RealR1_client.rs', 78, 80]
def
  RealR1_client.ProofAccountNonces.Insts.Aspis_r1_cost_probeProverAttemptSecretsProvider.attempt_secrets
  (self : RealR1_client.ProofAccountNonces) (k : Std.Usize) :
  Result ((core.result.Result
    aspis_prover.state_only_entropy.StateOnlyAttemptSecrets verifier.Error) ×
    RealR1_client.ProofAccountNonces)
  := do
  let a ← Array.index_usize self.nonces k
  let r ←
    aspis_prover.state_only_entropy.StateOnlyAttemptSecrets.generate_for_mask_nonce
      a
  let r1 ←
    core.result.Result.map_err
      RealR1_client.AttemptSecretsProviderProofAccountNonces.attempt_secrets.closure.Insts.CoreOpsFunctionFnOnceTupleStateOnlyAttemptEntropyErrorError
      r ()
  ok (r1, self)

end
end RW
end ProverPin2

#check @ProverPin2.RW.RealR1_client.ProofAccountNonces.Insts.Aspis_r1_cost_probeProverAttemptSecretsProvider.attempt_secrets
#print axioms ProverPin2.RW.RealR1_client.ProofAccountNonces.Insts.Aspis_r1_cost_probeProverAttemptSecretsProvider.attempt_secrets
-- 6 carried blocks, 0 new opaque items, 0 signature checks
