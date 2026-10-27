import R1Z.PV_RE_ComposedContextsGenerator5

set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RE_ComposedSuffix5_037
open Aeneas Aeneas.Std Result ControlFlow Error ProverRwFull
variable [ExternalTypes] [ExternalFuns]
private abbrev Payload {α : Type} (_ : Result α) := α

/-- The actual entire suffix after the first bind in `prover.semantic_error`.
Recursive calls remain the original extracted calls. -/
def continueAfter (e : r1_wire.Error) (out : Payload (r1_wire.Error.Insts.CoreCmpPartialEqError.eq e r1_wire.Error.ActivePole)) : Result verifier.Error := do
  let b := out
  if b
  then ok verifier.Error.Rejected
  else ok verifier.Error.Semantic


end R1Z.PV_RE_ComposedSuffix5_037
pv_composed5_source_contexts ProverRwFull.prover.semantic_error
pv_composed5_source_contexts R1Z.PV_RE_ComposedSuffix5_037.continueAfter

set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RE_ComposedSuffix5_038
open Aeneas Aeneas.Std Result ControlFlow Error ProverRwFull
variable [ExternalTypes] [ExternalFuns]
private abbrev Payload {α : Type} (_ : Result α) := α

/-- The actual entire suffix after the first bind in `RealR1_client.prove_for_proof_accounts`.
Recursive calls remain the original extracted calls. -/
def continueAfter {T0 : Type} (coreopsfunctionFnMutT0TupleUsizeArrayU832Inst :
  core.ops.function.FnMut T0 Std.Usize (Array Std.U8 32#usize)) (public1 : aspis_statement.pool_v1.pair_forest_semantic_terminal.r0.Public) (compiled :
  aspis_statement.pool_v1.pair_forest_trace.PoolV1PairForestMergedC1CompilationV1) (hash : Slice (Slice Std.U8) → Result (Array Std.U8 32#usize)) (nonce_store :
  aspis_prover.state_only_entropy.DurableStateOnlyMaskNonceStore) (proof_account : T0) (out : Payload (prover.prove_masked_retrying_with
      (RealR1_client.prove_for_proof_accounts.closure.Insts.CoreOpsFunctionFnMutTupleUsizeResultStateOnlyAttemptSecretsError
      coreopsfunctionFnMutT0TupleUsizeArrayU832Inst) public1 compiled
      transport.Variant.S2 hash nonce_store proof_account)) : Result ((core.result.Result prover.RetriedProof verifier.Error) ×
    aspis_prover.state_only_entropy.DurableStateOnlyMaskNonceStore) := do
  let (r, nonce_store1) := out
  ok (r, nonce_store1)



end R1Z.PV_RE_ComposedSuffix5_038
pv_composed5_source_contexts ProverRwFull.RealR1_client.prove_for_proof_accounts
pv_composed5_source_contexts R1Z.PV_RE_ComposedSuffix5_038.continueAfter

set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RE_ComposedSuffix5_039
open Aeneas Aeneas.Std Result ControlFlow Error ProverRwFull
variable [ExternalTypes] [ExternalFuns]
private abbrev Payload {α : Type} (_ : Result α) := α

/-- The actual entire suffix after the first bind in `RealR1_client.prove_for_proof_accounts.closure.Insts.CoreOpsFunctionFnOnceTupleUsizeResultStateOnlyAttemptSecretsError.call_once`.
Recursive calls remain the original extracted calls. -/
def continueAfter {T0 : Type} (coreopsfunctionFnMutT0TupleUsizeArrayU832Inst :
  core.ops.function.FnMut T0 Std.Usize (Array Std.U8 32#usize)) (c : RealR1_client.prove_for_proof_accounts.closure T0) (i : Std.Usize) (out : Payload (RealR1_client.prove_for_proof_accounts.closure.Insts.CoreOpsFunctionFnMutTupleUsizeResultStateOnlyAttemptSecretsError.call_mut
      coreopsfunctionFnMutT0TupleUsizeArrayU832Inst c i)) : Result ((core.result.Result
    aspis_prover.state_only_entropy.StateOnlyAttemptSecrets verifier.Error) ×
    (RealR1_client.prove_for_proof_accounts.closure T0)) := do
  let (r, c1, call_mut_back) := out
  ok (r, call_mut_back c1)


end R1Z.PV_RE_ComposedSuffix5_039
pv_composed5_source_contexts ProverRwFull.RealR1_client.prove_for_proof_accounts.closure.Insts.CoreOpsFunctionFnOnceTupleUsizeResultStateOnlyAttemptSecretsError.call_once
pv_composed5_source_contexts R1Z.PV_RE_ComposedSuffix5_039.continueAfter

set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RE_ComposedSuffix5_040
open Aeneas Aeneas.Std Result ControlFlow Error ProverRwFull
variable [ExternalTypes] [ExternalFuns]
private abbrev Payload {α : Type} (_ : Result α) := α

/-- The actual entire suffix after the first bind in `aspis_prover.state_only_entropy.DurableStateOnlyMaskNonceStore.Insts.Aspis_proverState_only_hidingStateOnlyMaskNonceStore.reserve`.
Recursive calls remain the original extracted calls. -/
def continueAfter (self : aspis_prover.state_only_entropy.DurableStateOnlyMaskNonceStore) (statement_digest : Array Std.U8 32#usize) (mask_nonce : Array Std.U8 32#usize) (out : Payload (aspis_prover.state_only_entropy.DurableStateOnlyMaskNonceStore.reserve_fallible
      self statement_digest mask_nonce)) : Result (Bool ×
    aspis_prover.state_only_entropy.DurableStateOnlyMaskNonceStore) := do
  let (r, self1) := out
  match r with
  | core.result.Result.Ok reserved => ok (reserved, self1)
  | core.result.Result.Err error =>
    let ek ← std.io.error.Error.kind error
    ok (false, { self1 with last_error := (some ek) })


end R1Z.PV_RE_ComposedSuffix5_040
pv_composed5_source_contexts ProverRwFull.aspis_prover.state_only_entropy.DurableStateOnlyMaskNonceStore.Insts.Aspis_proverState_only_hidingStateOnlyMaskNonceStore.reserve
pv_composed5_source_contexts R1Z.PV_RE_ComposedSuffix5_040.continueAfter

set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RE_ComposedSuffix5_041
open Aeneas Aeneas.Std Result ControlFlow Error ProverRwFull
variable [ExternalTypes] [ExternalFuns]
private abbrev Payload {α : Type} (_ : Result α) := α

/-- The actual entire suffix after the first bind in `aspis_prover.state_only_entropy.DurableStateOnlyMaskNonceStore.reserve_fallible`.
Recursive calls remain the original extracted calls. -/
def continueAfter (self : aspis_prover.state_only_entropy.DurableStateOnlyMaskNonceStore) (statement_digest : Array Std.U8 32#usize) (mask_nonce : Array Std.U8 32#usize) (out : Payload (aspis_prover.state_only_entropy.DurableStateOnlyMaskNonceStore.reservation_path
      { self with last_error := none } mask_nonce)) : Result ((core.result.Result Bool std.io.error.Error) ×
    aspis_prover.state_only_entropy.DurableStateOnlyMaskNonceStore) := do
  let path := out
  let options ← std.fs.OpenOptions.new
  let (oo, write_back) ← std.fs.OpenOptions.write options true
  let (oo1, create_new_back) ← std.fs.OpenOptions.create_new oo true
  let oo2 := create_new_back oo1
  let options1 := write_back oo2
  let (oo3, mode_back) ←
    std.fs.OpenOptions.Insts.StdOsUnixFsOpenOptionsExt.mode options1 384#u32
  let options2 := mode_back oo3
  let r ←
    std.fs.OpenOptions.open std.path.PathBuf.Insts.CoreConvertAsRefPath
      options2 path
  match r with
  | core.result.Result.Ok file =>
    let s ←
      Aeneas.Std.lift (Array.to_slice aspis_prover.state_only_entropy.RESERVATION_MAGIC)
    let (r1, file1) ←
      std.fs.File.Insts.StdIoWrite.write_all file s
    let cf ← core.result.Result.Insts.CoreOpsTry.branch r1
    match cf with
    | core.ops.control_flow.ControlFlow.Continue _ =>
      let s1 ← Aeneas.Std.lift (Array.to_slice statement_digest)
      let (r2, file2) ←
        std.fs.File.Insts.StdIoWrite.write_all file1 s1
      let cf1 ← core.result.Result.Insts.CoreOpsTry.branch r2
      match cf1 with
      | core.ops.control_flow.ControlFlow.Continue _ =>
        let s2 ← Aeneas.Std.lift (Array.to_slice mask_nonce)
        let (r3, file3) ←
          std.fs.File.Insts.StdIoWrite.write_all file2 s2
        let cf2 ← core.result.Result.Insts.CoreOpsTry.branch r3
        match cf2 with
        | core.ops.control_flow.ControlFlow.Continue _ =>
          let r4 ← std.fs.File.sync_all file3
          let cf3 ← core.result.Result.Insts.CoreOpsTry.branch r4
          match cf3 with
          | core.ops.control_flow.ControlFlow.Continue _ =>
            let p ←
              std.path.PathBuf.Insts.CoreOpsDerefDerefPath.deref self.directory
            let r5 ← aspis_prover.state_only_entropy.sync_directory p
            let cf4 ← core.result.Result.Insts.CoreOpsTry.branch r5
            match cf4 with
            | core.ops.control_flow.ControlFlow.Continue _ =>
              ok (core.result.Result.Ok true, { self with last_error := none })
            | core.ops.control_flow.ControlFlow.Break residual =>
              let r6 ←
                core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
                  Bool (core.convert.FromSame std.io.error.Error) residual
              ok (r6, { self with last_error := none })
          | core.ops.control_flow.ControlFlow.Break residual =>
            let r5 ←
              core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
                Bool (core.convert.FromSame std.io.error.Error) residual
            ok (r5, { self with last_error := none })
        | core.ops.control_flow.ControlFlow.Break residual =>
          let r4 ←
            core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
              Bool (core.convert.FromSame std.io.error.Error) residual
          ok (r4, { self with last_error := none })
      | core.ops.control_flow.ControlFlow.Break residual =>
        let r3 ←
          core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
            Bool (core.convert.FromSame std.io.error.Error) residual
        ok (r3, { self with last_error := none })
    | core.ops.control_flow.ControlFlow.Break residual =>
      let r2 ←
        core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
          Bool (core.convert.FromSame std.io.error.Error) residual
      ok (r2, { self with last_error := none })
  | core.result.Result.Err error =>
    let ek ← std.io.error.Error.kind error
    let b ←
      core.io.error.ErrorKind.Insts.CoreCmpPartialEqErrorKind.eq ek
        core.io.error.ErrorKind.AlreadyExists
    let r1 ←
      if b
      then ok (core.result.Result.Ok false)
      else ok (core.result.Result.Err error)
    ok (r1, { self with last_error := none })


end R1Z.PV_RE_ComposedSuffix5_041
pv_composed5_source_contexts ProverRwFull.aspis_prover.state_only_entropy.DurableStateOnlyMaskNonceStore.reserve_fallible
pv_composed5_source_contexts R1Z.PV_RE_ComposedSuffix5_041.continueAfter

set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RE_ComposedSuffix5_042
open Aeneas Aeneas.Std Result ControlFlow Error ProverRwFull
variable [ExternalTypes] [ExternalFuns]
private abbrev Payload {α : Type} (_ : Result α) := α

/-- The actual entire suffix after the first bind in `aspis_prover.state_only_entropy.Profile21SourceExpander.m31`.
Recursive calls remain the original extracted calls. -/
def continueAfter (self : aspis_prover.state_only_entropy.Profile21SourceExpander) (out : Payload (aspis_prover.state_only_entropy.Profile21SourceExpander.m31_loop self 0#i32)) : Result ((core.result.Result aspis_core.field.M31
    aspis_prover.state_only_hiding.StateOnlyMaskBuildError) ×
    aspis_prover.state_only_entropy.Profile21SourceExpander) := do
  let (self1, pending_return) := out
  match pending_return with
  | none =>
    ok (core.result.Result.Err
      aspis_prover.state_only_hiding.StateOnlyMaskBuildError.MaskSampleExhausted,
      self1)
  | some r => ok (r, self1)


end R1Z.PV_RE_ComposedSuffix5_042
pv_composed5_source_contexts ProverRwFull.aspis_prover.state_only_entropy.Profile21SourceExpander.m31
pv_composed5_source_contexts R1Z.PV_RE_ComposedSuffix5_042.continueAfter

set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RE_ComposedSuffix5_043
open Aeneas Aeneas.Std Result ControlFlow Error ProverRwFull
variable [ExternalTypes] [ExternalFuns]
private abbrev Payload {α : Type} (_ : Result α) := α

/-- The actual entire suffix after the first bind in `aspis_prover.state_only_entropy.Profile21SourceExpander.qm31`.
Recursive calls remain the original extracted calls. -/
def continueAfter (self : aspis_prover.state_only_entropy.Profile21SourceExpander) (out : Payload (aspis_prover.state_only_entropy.Profile21SourceExpander.m31 self)) : Result ((core.result.Result aspis_core.field.QM31
    aspis_prover.state_only_hiding.StateOnlyMaskBuildError) ×
    aspis_prover.state_only_entropy.Profile21SourceExpander) := do
  let (r, self1) := out
  let cf ← core.result.Result.Insts.CoreOpsTry.branch r
  match cf with
  | core.ops.control_flow.ControlFlow.Continue val =>
    let (r1, self2) ←
      aspis_prover.state_only_entropy.Profile21SourceExpander.m31 self1
    let cf1 ← core.result.Result.Insts.CoreOpsTry.branch r1
    match cf1 with
    | core.ops.control_flow.ControlFlow.Continue val1 =>
      let c ← aspis_core.field.CM31.new val val1
      let (r2, self3) ←
        aspis_prover.state_only_entropy.Profile21SourceExpander.m31 self2
      let cf2 ← core.result.Result.Insts.CoreOpsTry.branch r2
      match cf2 with
      | core.ops.control_flow.ControlFlow.Continue val2 =>
        let (r3, self4) ←
          aspis_prover.state_only_entropy.Profile21SourceExpander.m31 self3
        let cf3 ← core.result.Result.Insts.CoreOpsTry.branch r3
        match cf3 with
        | core.ops.control_flow.ControlFlow.Continue val3 =>
          let c1 ← aspis_core.field.CM31.new val2 val3
          ok (core.result.Result.Ok { c0 := c, c1 }, self4)
        | core.ops.control_flow.ControlFlow.Break residual =>
          let r4 ←
            core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
              aspis_core.field.QM31 (core.convert.FromSame
              aspis_prover.state_only_hiding.StateOnlyMaskBuildError) residual
          ok (r4, self4)
      | core.ops.control_flow.ControlFlow.Break residual =>
        let r3 ←
          core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
            aspis_core.field.QM31 (core.convert.FromSame
            aspis_prover.state_only_hiding.StateOnlyMaskBuildError) residual
        ok (r3, self3)
    | core.ops.control_flow.ControlFlow.Break residual =>
      let r2 ←
        core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
          aspis_core.field.QM31 (core.convert.FromSame
          aspis_prover.state_only_hiding.StateOnlyMaskBuildError) residual
      ok (r2, self2)
  | core.ops.control_flow.ControlFlow.Break residual =>
    let r1 ←
      core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
        aspis_core.field.QM31 (core.convert.FromSame
        aspis_prover.state_only_hiding.StateOnlyMaskBuildError) residual
    ok (r1, self1)


end R1Z.PV_RE_ComposedSuffix5_043
pv_composed5_source_contexts ProverRwFull.aspis_prover.state_only_entropy.Profile21SourceExpander.qm31
pv_composed5_source_contexts R1Z.PV_RE_ComposedSuffix5_043.continueAfter

set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RE_ComposedSuffix5_044
open Aeneas Aeneas.Std Result ControlFlow Error ProverRwFull
variable [ExternalTypes] [ExternalFuns]
private abbrev Payload {α : Type} (_ : Result α) := α

/-- The actual entire suffix after the first bind in `aspis_prover.state_only_entropy.ReservedStateOnlyAttemptSecrets.derive_pool_v1_leaf_salt`.
Recursive calls remain the original extracted calls. -/
def continueAfter (self : aspis_prover.state_only_entropy.ReservedStateOnlyAttemptSecrets) (hash : Slice (Slice Std.U8) → Result (Array Std.U8 32#usize)) (context : aspis_core.state_only_hiding.StateOnlyHidingContext) (tree_tag : Std.U8) (leaf_index : Std.U32) (out : Payload (aspis_prover.state_only_entropy.ReservedStateOnlyAttemptSecrets.validate_pool_v1_context
      self context)) : Result (core.result.Result (Array Std.U8 32#usize)
    aspis_prover.state_only_hiding.StateOnlyMaskBuildError) := do
  let r := out
  let cf ← core.result.Result.Insts.CoreOpsTry.branch r
  match cf with
  | core.ops.control_flow.ControlFlow.Continue _ =>
    let attempt_binding ←
      aspis_prover.state_only_entropy.pool_v1_private_attempt_binding hash
        self.precommit_binding context
    let s ← Aeneas.Std.lift (Array.to_slice attempt_binding)
    let s1 ← Aeneas.Std.lift (Array.to_slice self.mask_nonce)
    let s2 ← Aeneas.Std.lift (Array.to_slice (Array.make 1#usize [ tree_tag ]))
    let a ← Aeneas.Std.lift (core.num.U32.to_le_bytes leaf_index)
    let s3 ← Aeneas.Std.lift (Array.to_slice a)
    let s4 ←
      zeroize.Zeroizing.Insts.CoreConvertAsRef.as_ref
        (Array.Insts.CoreConvertAsRefSlice Std.U8 32#usize)
        (Array.Insts.ZeroizeZeroize 32#usize (zeroize.Zeroize.Blanket
        U8.Insts.ZeroizeDefaultIsZeroes)) self.leaf_salt_seed
    let s5 ←
      Aeneas.Std.lift (Array.to_slice
        (Array.make 6#usize [
          aspis_prover.state_only_entropy.LEAF_SALT_DOMAIN, s, s1, s2, s3, s4
          ]))
    let a1 ← hash s5
    ok (core.result.Result.Ok a1)
  | core.ops.control_flow.ControlFlow.Break residual =>
    core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
      (Array Std.U8 32#usize) (core.convert.FromSame
      aspis_prover.state_only_hiding.StateOnlyMaskBuildError) residual


end R1Z.PV_RE_ComposedSuffix5_044
pv_composed5_source_contexts ProverRwFull.aspis_prover.state_only_entropy.ReservedStateOnlyAttemptSecrets.derive_pool_v1_leaf_salt
pv_composed5_source_contexts R1Z.PV_RE_ComposedSuffix5_044.continueAfter

set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RE_ComposedSuffix5_045
open Aeneas Aeneas.Std Result ControlFlow Error ProverRwFull
variable [ExternalTypes] [ExternalFuns]
private abbrev Payload {α : Type} (_ : Result α) := α

/-- The actual entire suffix after the first bind in `aspis_prover.state_only_entropy.ReservedStateOnlyAttemptSecrets.derive_pool_v1_zero_factor_d`.
Recursive calls remain the original extracted calls. -/
def continueAfter (self : aspis_prover.state_only_entropy.ReservedStateOnlyAttemptSecrets) (hash : Slice (Slice Std.U8) → Result (Array Std.U8 32#usize)) (context : aspis_core.state_only_hiding.StateOnlyHidingContext) (expected_factor_fingerprint : Std.U64) (active_masks : Array Std.U16 64#usize) (out : Payload (aspis_prover.state_only_entropy.ReservedStateOnlyAttemptSecrets.validate_pool_v1_context
      self context)) : Result (core.result.Result (alloc.vec.Vec aspis_core.field.QM31)
    aspis_prover.state_only_hiding.StateOnlyMaskBuildError) := do
  let r := out
  let cf ← core.result.Result.Insts.CoreOpsTry.branch r
  match cf with
  | core.ops.control_flow.ControlFlow.Continue _ =>
    if context.layout_factor_fingerprint != expected_factor_fingerprint
    then
      ok (core.result.Result.Err
        aspis_prover.state_only_hiding.StateOnlyMaskBuildError.Layout)
    else
      let attempt_binding ←
        aspis_prover.state_only_entropy.pool_v1_private_attempt_binding hash
          self.precommit_binding context
      let s ← Aeneas.Std.lift (Array.to_slice attempt_binding)
      let s1 ←
        zeroize.Zeroizing.Insts.CoreConvertAsRef.as_ref
          (Array.Insts.CoreConvertAsRefSlice Std.U8 32#usize)
          (Array.Insts.ZeroizeZeroize 32#usize (zeroize.Zeroize.Blanket
          U8.Insts.ZeroizeDefaultIsZeroes)) self.source_mask_seed
      let s2 ←
        Aeneas.Std.lift (Array.to_slice
          (Array.make 3#usize [
            aspis_prover.state_only_entropy.POOL_V1_D_SEED_DOMAIN, s, s1
            ]))
      let a ← hash s2
      let expander ←
        aspis_prover.state_only_entropy.Profile21SourceExpander.new hash a
      let (r1, _) ← aspis_prover.state_only_entropy.sample_source_d expander
      let cf1 ← core.result.Result.Insts.CoreOpsTry.branch r1
      match cf1 with
      | core.ops.control_flow.ControlFlow.Continue val =>
        let active ←
          aspis_prover.state_only_entropy.source_active_flags active_masks
        let (s3, deref_mut_back) ← Aeneas.Std.lift (alloc.vec.Vec.deref_mut val)
        let (r2, s4) ←
          aspis_prover.state_only_entropy.balance_source_d s3 active
        let cf2 ← core.result.Result.Insts.CoreOpsTry.branch r2
        match cf2 with
        | core.ops.control_flow.ControlFlow.Continue _ =>
          let v := deref_mut_back s4
          let (v1, _) ←
            core.mem.take (alloc.vec.Vec.Insts.CoreDefaultDefault
              aspis_core.field.QM31) v
          ok (core.result.Result.Ok v1)
        | core.ops.control_flow.ControlFlow.Break residual =>
          core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
            (alloc.vec.Vec aspis_core.field.QM31) (core.convert.FromSame
            aspis_prover.state_only_hiding.StateOnlyMaskBuildError) residual
      | core.ops.control_flow.ControlFlow.Break residual =>
        core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
          (alloc.vec.Vec aspis_core.field.QM31) (core.convert.FromSame
          aspis_prover.state_only_hiding.StateOnlyMaskBuildError) residual
  | core.ops.control_flow.ControlFlow.Break residual =>
    core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
      (alloc.vec.Vec aspis_core.field.QM31) (core.convert.FromSame
      aspis_prover.state_only_hiding.StateOnlyMaskBuildError) residual


end R1Z.PV_RE_ComposedSuffix5_045
pv_composed5_source_contexts ProverRwFull.aspis_prover.state_only_entropy.ReservedStateOnlyAttemptSecrets.derive_pool_v1_zero_factor_d
pv_composed5_source_contexts R1Z.PV_RE_ComposedSuffix5_045.continueAfter

set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RE_ComposedSuffix5_046
open Aeneas Aeneas.Std Result ControlFlow Error ProverRwFull
variable [ExternalTypes] [ExternalFuns]
private abbrev Payload {α : Type} (_ : Result α) := α

/-- The actual entire suffix after the first bind in `aspis_prover.state_only_hiding.apply_pool_v1_pair_forest_h1_padding_mask_v1`.
Recursive calls remain the original extracted calls. -/
def continueAfter (h1 : Slice aspis_core.field.QM31) (padding : Slice aspis_core.field.QM31) (out : Payload (aspis_prover.state_only_hiding.pool_v1_pair_forest_copy_active_rows)) : Result ((core.result.Result Unit
    aspis_prover.state_only_hiding.StateOnlyMaskBuildError) × (Slice
    aspis_core.field.QM31)) := do
  let r := out
  let cf ← core.result.Result.Insts.CoreOpsTry.branch r
  match cf with
  | core.ops.control_flow.ControlFlow.Continue val =>
    aspis_prover.state_only_hiding.apply_h1_padding_mask_for_active h1 padding
      val
  | core.ops.control_flow.ControlFlow.Break residual =>
    let r1 ←
      core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
        Unit (core.convert.FromSame
        aspis_prover.state_only_hiding.StateOnlyMaskBuildError) residual
    ok (r1, h1)


end R1Z.PV_RE_ComposedSuffix5_046
pv_composed5_source_contexts ProverRwFull.aspis_prover.state_only_hiding.apply_pool_v1_pair_forest_h1_padding_mask_v1
pv_composed5_source_contexts R1Z.PV_RE_ComposedSuffix5_046.continueAfter

set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RE_ComposedSuffix5_047
open Aeneas Aeneas.Std Result ControlFlow Error ProverRwFull
variable [ExternalTypes] [ExternalFuns]
private abbrev Payload {α : Type} (_ : Result α) := α

/-- The actual entire suffix after the first bind in `host_commitment.Commitment.fill_opening`.
Recursive calls remain the original extracted calls. -/
def continueAfter (self : host_commitment.Commitment) (u : aspis_core.r0.domain.FibreIndex) (out : aspis_core.r0.wire.FibreOpening) (pvBoundValue : Payload (host_commitment.fill_opening_values self u out.values 0#usize)) : Result aspis_core.r0.wire.FibreOpening := do
  let a := pvBoundValue
  let path ← host_commitment.opening_path self.time
  let a1 := Array.repeat 32#usize 0#u8
  let a2 := Array.repeat 7#usize a1
  let a3 := Array.repeat 6#usize a2
  let a4 ← Array.update out.paths path a3
  ok { values := a, paths := a4 }


end R1Z.PV_RE_ComposedSuffix5_047
pv_composed5_source_contexts ProverRwFull.host_commitment.Commitment.fill_opening
pv_composed5_source_contexts R1Z.PV_RE_ComposedSuffix5_047.continueAfter

set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RE_ComposedSuffix5_048
open Aeneas Aeneas.Std Result ControlFlow Error ProverRwFull
variable [ExternalTypes] [ExternalFuns]
private abbrev Payload {α : Type} (_ : Result α) := α

/-- The actual entire suffix after the first bind in `host_commitment.EncodingDomain.new`.
Recursive calls remain the original extracted calls. -/
def continueAfter  (out : Payload (host_commitment.domain_points)) : Result (core.result.Result host_commitment.EncodingDomain
    aspis_core.r0.Error) := do
  let r := out
  let cf ← core.result.Result.Insts.CoreOpsTry.branch r
  match cf with
  | core.ops.control_flow.ControlFlow.Continue val =>
    let (r1, levels) ←
      alloc.vec.Vec.try_reserve_exact Global (alloc.vec.Vec.new (alloc.vec.Vec
        aspis_core.field.M31)) 9#usize
    let r2 ←
      core.result.Result.map_err
        host_commitment.EncodingDomain.new.closure.Insts.CoreOpsFunctionFnOnceTupleTryReserveErrorError
        r1 ()
    let cf1 ← core.result.Result.Insts.CoreOpsTry.branch r2
    match cf1 with
    | core.ops.control_flow.ControlFlow.Continue _ =>
      let s := alloc.vec.Vec.deref val
      let r3 ← host_commitment.domain_first_level s
      let cf2 ← core.result.Result.Insts.CoreOpsTry.branch r3
      match cf2 with
      | core.ops.control_flow.ControlFlow.Continue val1 =>
        let levels1 ← alloc.vec.Vec.push levels val1
        let r4 ← host_commitment.domain_append_levels levels1 0#usize
        let cf3 ← core.result.Result.Insts.CoreOpsTry.branch r4
        match cf3 with
        | core.ops.control_flow.ControlFlow.Continue val2 =>
          ok (core.result.Result.Ok { xy := val, levels := val2 })
        | core.ops.control_flow.ControlFlow.Break residual =>
          core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
            host_commitment.EncodingDomain (core.convert.FromSame
            aspis_core.r0.Error) residual
      | core.ops.control_flow.ControlFlow.Break residual =>
        core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
          host_commitment.EncodingDomain (core.convert.FromSame
          aspis_core.r0.Error) residual
    | core.ops.control_flow.ControlFlow.Break residual =>
      core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
        host_commitment.EncodingDomain (core.convert.FromSame
        aspis_core.r0.Error) residual
  | core.ops.control_flow.ControlFlow.Break residual =>
    core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
      host_commitment.EncodingDomain (core.convert.FromSame
      aspis_core.r0.Error) residual


end R1Z.PV_RE_ComposedSuffix5_048
pv_composed5_source_contexts ProverRwFull.host_commitment.EncodingDomain.new
pv_composed5_source_contexts R1Z.PV_RE_ComposedSuffix5_048.continueAfter

set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RE_ComposedSuffix5_049
open Aeneas Aeneas.Std Result ControlFlow Error ProverRwFull
variable [ExternalTypes] [ExternalFuns]
private abbrev Payload {α : Type} (_ : Result α) := α

/-- The actual entire suffix after the first bind in `host_commitment.encode_commitment_words.closure_1.Insts.CoreOpsFunctionFnMutTupleUsizeResultWordError.call_mut`.
Recursive calls remain the original extracted calls. -/
def continueAfter (state : host_commitment.encode_commitment_words.closure_1) (args : Std.Usize) (out : Payload (host_commitment.encode_commitment_words.closure_1.Insts.CoreOpsFunctionFnTupleUsizeResultWordError.call
      state args)) : Result ((core.result.Result host_commitment.Word aspis_core.r0.Error) ×
    host_commitment.encode_commitment_words.closure_1) := do
  let r := out
  ok (r, state)


end R1Z.PV_RE_ComposedSuffix5_049
pv_composed5_source_contexts ProverRwFull.host_commitment.encode_commitment_words.closure_1.Insts.CoreOpsFunctionFnMutTupleUsizeResultWordError.call_mut
pv_composed5_source_contexts R1Z.PV_RE_ComposedSuffix5_049.continueAfter

set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RE_ComposedSuffix5_050
open Aeneas Aeneas.Std Result ControlFlow Error ProverRwFull
variable [ExternalTypes] [ExternalFuns]
private abbrev Payload {α : Type} (_ : Result α) := α

/-- The actual entire suffix after the first bind in `host_commitment.encode_commitment_words.closure_1.Insts.CoreOpsFunctionFnOnceTupleUsizeResultWordError.call_once`.
Recursive calls remain the original extracted calls. -/
def continueAfter (c : host_commitment.encode_commitment_words.closure_1) (i : Std.Usize) (out : Payload (host_commitment.encode_commitment_words.closure_1.Insts.CoreOpsFunctionFnMutTupleUsizeResultWordError.call_mut
      c i)) : Result (core.result.Result host_commitment.Word aspis_core.r0.Error) := do
  let (r, _) := out
  ok r


end R1Z.PV_RE_ComposedSuffix5_050
pv_composed5_source_contexts ProverRwFull.host_commitment.encode_commitment_words.closure_1.Insts.CoreOpsFunctionFnOnceTupleUsizeResultWordError.call_once
pv_composed5_source_contexts R1Z.PV_RE_ComposedSuffix5_050.continueAfter

set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RE_ComposedSuffix5_051
open Aeneas Aeneas.Std Result ControlFlow Error ProverRwFull
variable [ExternalTypes] [ExternalFuns]
private abbrev Payload {α : Type} (_ : Result α) := α

/-- The actual entire suffix after the first bind in `host_commitment.validate_commitment_lanes`.
Recursive calls remain the original extracted calls. -/
def continueAfter (messages : Slice (Array aspis_core.field.wide_exact.WideExact 1024#usize)) (lanes : Slice Std.Usize) (out : Payload (host_commitment.validate_commitment_lanes_loop messages lanes 0#usize)) : Result (core.result.Result Unit aspis_core.r0.Error) := do
  let pending_return := out
  match pending_return with
  | none => ok (core.result.Result.Ok ())
  | some r => ok r


end R1Z.PV_RE_ComposedSuffix5_051
pv_composed5_source_contexts ProverRwFull.host_commitment.validate_commitment_lanes
pv_composed5_source_contexts R1Z.PV_RE_ComposedSuffix5_051.continueAfter

set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RE_ComposedSuffix5_052
open Aeneas Aeneas.Std Result ControlFlow Error ProverRwFull
variable [ExternalTypes] [ExternalFuns]
private abbrev Payload {α : Type} (_ : Result α) := α

/-- The actual entire suffix after the first bind in `host_compact.compact_semantic_row`.
Recursive calls remain the original extracted calls. -/
def continueAfter (logical : Slice Std.U8) (out : alloc.vec.Vec Std.U8) (row : Std.U8) (at1 : Std.Usize) (pvBoundValue : Payload (r1_wire.row_shape row)) : Result ((core.result.Result Std.Usize compact.CodecError) × (alloc.vec.Vec
    Std.U8)) := do
  let o := pvBoundValue
  let r ← core.option.Option.ok_or o compact.CodecError.Length
  let cf ← core.result.Result.Insts.CoreOpsTry.branch r
  match cf with
  | core.ops.control_flow.ControlFlow.Continue val =>
    let (_, size) := val
    let i ← Aeneas.Std.lift (Std.Usize.wrapping_add at1 5#usize)
    let s ←
      core.slice.index.Slice.index (core.slice.index.SliceIndexRangeUsizeSlice
        Std.U8) logical { start := at1, «end» := i }
    let out1 ← alloc.vec.Vec.extend_from_slice core.clone.CloneU8 out s
    let at2 ← Aeneas.Std.lift (Std.Usize.wrapping_add at1 5#usize)
    let b ← host_compact.compact_row row
    if b
    then
      let i1 ← Aeneas.Std.lift (Std.Usize.wrapping_add at2 size)
      let s1 ←
        core.slice.index.Slice.index
          (core.slice.index.SliceIndexRangeUsizeSlice Std.U8) logical
          { start := at2, «end» := i1 }
      let (r1, out2) ← host_compact.compact_values s1 out1
      let cf1 ← core.result.Result.Insts.CoreOpsTry.branch r1
      match cf1 with
      | core.ops.control_flow.ControlFlow.Continue _ =>
        let i2 ← Aeneas.Std.lift (Std.Usize.wrapping_add at2 size)
        ok (core.result.Result.Ok i2, out2)
      | core.ops.control_flow.ControlFlow.Break residual =>
        let r2 ←
          core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
            Std.Usize (core.convert.FromSame compact.CodecError) residual
        ok (r2, out2)
    else
      let i1 ← Aeneas.Std.lift (Std.Usize.wrapping_add at2 size)
      let s1 ←
        core.slice.index.Slice.index
          (core.slice.index.SliceIndexRangeUsizeSlice Std.U8) logical
          { start := at2, «end» := i1 }
      let out2 ← alloc.vec.Vec.extend_from_slice core.clone.CloneU8 out1 s1
      let i2 ← Aeneas.Std.lift (Std.Usize.wrapping_add at2 size)
      ok (core.result.Result.Ok i2, out2)
  | core.ops.control_flow.ControlFlow.Break residual =>
    let r1 ←
      core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
        Std.Usize (core.convert.FromSame compact.CodecError) residual
    ok (r1, out)


end R1Z.PV_RE_ComposedSuffix5_052
pv_composed5_source_contexts ProverRwFull.host_compact.compact_semantic_row
pv_composed5_source_contexts R1Z.PV_RE_ComposedSuffix5_052.continueAfter

set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RE_ComposedSuffix5_053
open Aeneas Aeneas.Std Result ControlFlow Error ProverRwFull
variable [ExternalTypes] [ExternalFuns]
private abbrev Payload {α : Type} (_ : Result α) := α

/-- The actual entire suffix after the first bind in `host_semantic.SemanticOracle.Insts.Aspis_r1_cost_probeHost_sumcheckOracle.evaluate`.
Recursive calls remain the original extracted calls. -/
def continueAfter (self : host_semantic.SemanticOracle) (point : Array aspis_core.field.QM31 10#usize) (out : Payload (host_semantic.point_claims self.columns point)) : Result (core.result.Result aspis_core.field.QM31 r1_wire.Error) := do
  let r := out
  let cf ← core.result.Result.Insts.CoreOpsTry.branch r
  match cf with
  | core.ops.control_flow.ControlFlow.Continue val =>
    let r1 ←
      aspis_statement.pool_v1.pair_forest_semantic_terminal.r0.Public.terminal_qm31
        self.«public» val point self.challenges
    let r2 ←
      core.result.Result.map_err
        host_semantic.OracleSemanticOracle.evaluate.closure.Insts.CoreOpsFunctionFnOnceTupleErrorError
        r1 ()
    let cf1 ← core.result.Result.Insts.CoreOpsTry.branch r2
    match cf1 with
    | core.ops.control_flow.ControlFlow.Continue val1 =>
      let a ← Array.index_usize val 0#usize
      let mask ← host_semantic.claim_mask_value a point
      let q ← aspis_core.field.QM31.mul self.eta val1
      let q1 ← aspis_core.field.QM31.add mask q
      let q2 ← Array.index_usize point 8#usize
      let q3 ← Array.index_usize point 9#usize
      let q4 ← host_semantic.extra self.d q2 q3
      let q5 ← aspis_core.field.QM31.add q1 q4
      ok (core.result.Result.Ok q5)
    | core.ops.control_flow.ControlFlow.Break residual =>
      core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
        aspis_core.field.QM31 (core.convert.FromSame r1_wire.Error) residual
  | core.ops.control_flow.ControlFlow.Break residual =>
    core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
      aspis_core.field.QM31 (core.convert.FromSame r1_wire.Error) residual


end R1Z.PV_RE_ComposedSuffix5_053
pv_composed5_source_contexts ProverRwFull.host_semantic.SemanticOracle.Insts.Aspis_r1_cost_probeHost_sumcheckOracle.evaluate
pv_composed5_source_contexts R1Z.PV_RE_ComposedSuffix5_053.continueAfter

set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RE_ComposedSuffix5_054
open Aeneas Aeneas.Std Result ControlFlow Error ProverRwFull
variable [ExternalTypes] [ExternalFuns]
private abbrev Payload {α : Type} (_ : Result α) := α

/-- The actual entire suffix after the first bind in `host_semantic.add_d_tail`.
Recursive calls remain the original extracted calls. -/
def continueAfter (mask_sum : aspis_core.field.QM31) (dc : Array aspis_core.field.QM31 1024#usize) (out : Payload (host_semantic.d_tail_side dc 0#usize)) : Result aspis_core.field.QM31 := do
  let q := out
  let first ← aspis_core.field.QM31.mul_m31 q 512#u32
  let mask_sum1 ← aspis_core.field.QM31.add mask_sum first
  let q1 ← host_semantic.d_tail_side dc 28#usize
  let second ← aspis_core.field.QM31.mul_m31 q1 512#u32
  aspis_core.field.QM31.add mask_sum1 second


end R1Z.PV_RE_ComposedSuffix5_054
pv_composed5_source_contexts ProverRwFull.host_semantic.add_d_tail
pv_composed5_source_contexts R1Z.PV_RE_ComposedSuffix5_054.continueAfter

set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RE_ComposedSuffix5_055
open Aeneas Aeneas.Std Result ControlFlow Error ProverRwFull
variable [ExternalTypes] [ExternalFuns]
private abbrev Payload {α : Type} (_ : Result α) := α

/-- The actual entire suffix after the first bind in `host_semantic.build_with_helper_mode`.
Recursive calls remain the original extracted calls. -/
def continueAfter {H : Type} {T1 : Type} {T2 : Type} (aspis_coredigestDigest32Inst :
  aspis_core.digest.Digest32 H) (coreopsfunctionFnOnceT1PairQM31QM31ResultVecQM31ErrorInst :
  core.ops.function.FnOnce T1 (aspis_core.field.QM31 × aspis_core.field.QM31)
  (core.result.Result (alloc.vec.Vec aspis_core.field.QM31) r1_wire.Error)) (CommitmentsInst : host_semantic.Commitments T2) (public1 : aspis_statement.pool_v1.pair_forest_semantic_terminal.r0.Public) (c1 : Array (alloc.vec.Vec aspis_core.field.M31) 26#usize) (d : Array aspis_core.field.QM31 1024#usize) (g : Array aspis_core.field.QM31 1024#usize) (h1_padding : Array aspis_core.field.QM31 1024#usize) (helper : T1) (commitments : T2) (hash : H) (variant : transport.Variant) (out : Payload (host_semantic.check_semantic_columns c1 d g)) : Result ((core.result.Result (host_semantic.BuiltSemantics H) r1_wire.Error)
    × T2) := do
  let r := out
  let cf ← core.result.Result.Insts.CoreOpsTry.branch r
  match cf with
  | core.ops.control_flow.ControlFlow.Continue _ =>
    let (r1, commitments1) ← CommitmentsInst.c1 commitments c1 d
    let cf1 ← core.result.Result.Insts.CoreOpsTry.branch r1
    match cf1 with
    | core.ops.control_flow.ControlFlow.Continue val =>
      let r2 ←
        aspis_statement.pool_v1.pair_forest_semantic_terminal.r0.Public.public_bytes
          public1
      let r3 ←
        core.result.Result.map_err
          (host_semantic.build_with_helper_mode.closure.Insts.CoreOpsFunctionFnOnceTupleErrorError
          aspis_coredigestDigest32Inst
          coreopsfunctionFnOnceT1PairQM31QM31ResultVecQM31ErrorInst
          CommitmentsInst) r2 ()
      let cf2 ← core.result.Result.Insts.CoreOpsTry.branch r3
      match cf2 with
      | core.ops.control_flow.ControlFlow.Continue val1 =>
        let s := alloc.vec.Vec.deref val1
        let r4 ←
          host_wire.SemanticTranscript.new aspis_coredigestDigest32Inst hash s
            val
        let cf3 ← core.result.Result.Insts.CoreOpsTry.branch r4
        match cf3 with
        | core.ops.control_flow.ControlFlow.Continue val2 =>
          let s1 ← Aeneas.Std.lift (Array.to_slice val)
          let bytes ← alloc.slice.Slice.to_vec core.clone.CloneU8 s1
          let s2 ← Aeneas.Std.lift (Array.to_slice (Std.Array.empty Std.U8))
          let (r5, val3, bytes1) ←
            host_semantic.semantic_row aspis_coredigestDigest32Inst 0#u8 s2
              val2 bytes
          let cf4 ← core.result.Result.Insts.CoreOpsTry.branch r5
          match cf4 with
          | core.ops.control_flow.ControlFlow.Continue val4 =>
            let s3 ← Aeneas.Std.lift (Array.to_slice (Std.Array.empty Std.U8))
            let (r6, val5, bytes2) ←
              host_semantic.semantic_row aspis_coredigestDigest32Inst 1#u8 s3
                val3 bytes1
            let cf5 ← core.result.Result.Insts.CoreOpsTry.branch r6
            match cf5 with
            | core.ops.control_flow.ControlFlow.Continue val6 =>
              let r7 ←
                coreopsfunctionFnOnceT1PairQM31QM31ResultVecQM31ErrorInst.call_once
                  helper (val4, val6)
              let cf6 ← core.result.Result.Insts.CoreOpsTry.branch r7
              match cf6 with
              | core.ops.control_flow.ControlFlow.Continue val7 =>
                let (s4, deref_mut_back) ←
                  Aeneas.Std.lift (alloc.vec.Vec.deref_mut val7)
                let s5 ← Aeneas.Std.lift (Array.to_slice h1_padding)
                let (r8, s6) ←
                  aspis_prover.state_only_hiding.apply_pool_v1_pair_forest_h1_padding_mask_v1
                    s4 s5
                let r9 ←
                  core.result.Result.map_err
                    (host_semantic.build_with_helper_mode.closure_1.Insts.CoreOpsFunctionFnOnceTupleStateOnlyMaskBuildErrorError
                    aspis_coredigestDigest32Inst
                    coreopsfunctionFnOnceT1PairQM31QM31ResultVecQM31ErrorInst
                    CommitmentsInst) r8 ()
                let cf7 ← core.result.Result.Insts.CoreOpsTry.branch r9
                match cf7 with
                | core.ops.control_flow.ControlFlow.Continue _ =>
                  let val8 := deref_mut_back s6
                  let i := alloc.vec.Vec.len val8
                  if i != 1024#usize
                  then
                    ok (core.result.Result.Err r1_wire.Error.Public,
                      commitments1)
                  else
                    let s7 := alloc.vec.Vec.deref val8
                    let o ←
                      aspis_statement.state_only_semantic.state_only_copy_helper_sum
                        s7
                    let q ← aspis_core.field.QM31.ZERO
                    let b ←
                      core.cmp.PartialEq.ne.trait_default
                        (core.option.Option.Insts.CoreCmpPartialEqOption
                        aspis_core.field.QM31.Insts.CoreCmpPartialEqQM31) o
                        (some q)
                    if b
                    then
                      ok (core.result.Result.Err r1_wire.Error.Public,
                        commitments1)
                    else
                      let s8 := alloc.vec.Vec.deref val8
                      let (r10, commitments2) ←
                        CommitmentsInst.c2 commitments1 s8 g
                      let cf8 ←
                        core.result.Result.Insts.CoreOpsTry.branch r10
                      match cf8 with
                      | core.ops.control_flow.ControlFlow.Continue val9 =>
                        let s9 ← Aeneas.Std.lift (Array.to_slice val9)
                        let (r11, val10, bytes3) ←
                          host_semantic.semantic_row
                            aspis_coredigestDigest32Inst 2#u8 s9 val5 bytes2
                        let cf9 ←
                          core.result.Result.Insts.CoreOpsTry.branch r11
                        match cf9 with
                        | core.ops.control_flow.ControlFlow.Continue val11 =>
                          let (r12, val12, bytes4) ←
                            host_semantic.zc_rows aspis_coredigestDigest32Inst
                              val10 bytes3
                          let cf10 ←
                            core.result.Result.Insts.CoreOpsTry.branch r12
                          match cf10 with
                          | core.ops.control_flow.ControlFlow.Continue val13 =>
                            let s10 ←
                              Aeneas.Std.lift (Array.to_slice (Std.Array.empty Std.U8))
                            let (r13, val14, bytes5) ←
                              host_semantic.semantic_row
                                aspis_coredigestDigest32Inst 13#u8 s10 val12
                                bytes4
                            let cf11 ←
                              core.result.Result.Insts.CoreOpsTry.branch r13
                            match cf11 with
                            | core.ops.control_flow.ControlFlow.Continue val15
                              =>
                              let columns ←
                                host_semantic.lift_columns c1 val8 g d
                              let dc ←
                                transport.Variant.coefficients
                                  aspis_core.field.QM31.Insts.CoreMarkerCopy
                                  variant d
                              let mask_sum ←
                                host_semantic.initial_mask_sum columns
                              let mask_sum1 ←
                                host_semantic.add_d_tail mask_sum dc
                              let we ←
                                aspis_core.field.wide_exact.WideExact.from_qm31
                                  mask_sum1
                              let a ←
                                aspis_core.field.wide_exact.WideExact.to_le_bytes
                                  we
                              let s11 ← Aeneas.Std.lift (Array.to_slice a)
                              let (r14, val16, bytes6) ←
                                host_semantic.semantic_row
                                  aspis_coredigestDigest32Inst 14#u8 s11 val14
                                  bytes5
                              let cf12 ←
                                core.result.Result.Insts.CoreOpsTry.branch r14
                              match cf12 with
                              | core.ops.control_flow.ControlFlow.Continue
                                val17 =>
                                let (r15, val18, bytes7) ←
                                  host_sumcheck.prove_sumcheck
                                    aspis_coredigestDigest32Inst
                                    host_semantic.SemanticOracle.Insts.Aspis_r1_cost_probeHost_sumcheckOracle
                                    val16 bytes6 mask_sum1
                                    {
                                      «public» := public1,
                                      columns,
                                      challenges :=
                                        {
                                          lambda := val4,
                                          chi := val6,
                                          theta := val11,
                                          zc := val13,
                                          mu := val15,
                                          eta := val17
                                        },
                                      eta := val17,
                                      d := dc
                                    }
                                let cf13 ←
                                  core.result.Result.Insts.CoreOpsTry.branch
                                    r15
                                match cf13 with
                                | core.ops.control_flow.ControlFlow.Continue
                                  val19 =>
                                  let (alpha, _) := val19
                                  let r16 ←
                                    host_semantic.point_claims columns alpha
                                  let cf14 ←
                                    core.result.Result.Insts.CoreOpsTry.branch
                                      r16
                                  match cf14 with
                                  | core.ops.control_flow.ControlFlow.Continue
                                    val20 =>
                                    let state_before_z0 ←
                                      host_wire.SemanticTranscript.impl.state
                                        aspis_coredigestDigest32Inst val18
                                    let q1 ← Array.index_usize alpha 8#usize
                                    let q2 ← Array.index_usize alpha 9#usize
                                    let extras ←
                                      host_semantic.extra_claims columns
                                        variant q1 q2
                                    let v ←
                                      host_semantic.claim_bytes val20 extras
                                    let s12 := alloc.vec.Vec.deref v
                                    let r17 ← host_wire.record 25#u8 s12
                                    let cf15 ←
                                      core.result.Result.Insts.CoreOpsTry.branch
                                        r17
                                    match cf15 with
                                    |
                                      core.ops.control_flow.ControlFlow.Continue
                                      val21 =>
                                      let s13 := alloc.vec.Vec.deref val21
                                      let (r18, val22) ←
                                        host_wire.SemanticTranscript.challenge_reference_circle_point
                                          aspis_coredigestDigest32Inst val18
                                          25#u8 s13
                                      let cf16 ←
                                        core.result.Result.Insts.CoreOpsTry.branch
                                          r18
                                      match cf16 with
                                      |
                                        core.ops.control_flow.ControlFlow.Continue
                                        val23 =>
                                        let s14 := alloc.vec.Vec.deref val21
                                        let bytes8 ←
                                          alloc.vec.Vec.extend_from_slice
                                            core.clone.CloneU8 bytes7 s14
                                        let v1 ←
                                          host_semantic.endpoint_bytes columns
                                            variant val23
                                        let s15 := alloc.vec.Vec.deref v1
                                        let r19 ← host_wire.record 26#u8 s15
                                        let cf17 ←
                                          core.result.Result.Insts.CoreOpsTry.branch
                                            r19
                                        match cf17 with
                                        |
                                          core.ops.control_flow.ControlFlow.Continue
                                          val24 =>
                                          let s16 := alloc.vec.Vec.deref val24
                                          let (r20, val25) ←
                                            host_wire.SemanticTranscript.challenge_reference_circle_point
                                              aspis_coredigestDigest32Inst
                                              val22 26#u8 s16
                                          let cf18 ←
                                            core.result.Result.Insts.CoreOpsTry.branch
                                              r20
                                          match cf18 with
                                          |
                                            core.ops.control_flow.ControlFlow.Continue
                                            val26 =>
                                            let s17 :=
                                              alloc.vec.Vec.deref val24
                                            let bytes9 ←
                                              alloc.vec.Vec.extend_from_slice
                                                core.clone.CloneU8 bytes8 s17
                                            let b1 ←
                                              aspis_core.circle.SecureCirclePoint.Insts.CoreCmpPartialEqSecureCirclePoint.eq
                                                val23 val26
                                            if b1
                                            then
                                              ok (core.result.Result.Err
                                                r1_wire.Error.EqualCirclePoints,
                                                commitments2)
                                            else
                                              ok (core.result.Result.Ok
                                                {
                                                  bytes := bytes9,
                                                  transcript := val25,
                                                  challenges :=
                                                    {
                                                      lambda := val4,
                                                      chi := val6,
                                                      theta := val11,
                                                      zc := val13,
                                                      mu := val15,
                                                      eta := val17
                                                    },
                                                  alpha,
                                                  state_before_z0,
                                                  roots :=
                                                    (Array.make 2#usize [
                                                      val, val9
                                                      ]),
                                                  columns,
                                                  z :=
                                                    (Array.make 2#usize [
                                                      val23, val26
                                                      ])
                                                }, commitments2)
                                          |
                                            core.ops.control_flow.ControlFlow.Break
                                            residual =>
                                            let r21 ←
                                              core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
                                                (host_semantic.BuiltSemantics
                                                H) (core.convert.FromSame
                                                r1_wire.Error) residual
                                            ok (r21, commitments2)
                                        |
                                          core.ops.control_flow.ControlFlow.Break
                                          residual =>
                                          let r20 ←
                                            core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
                                              (host_semantic.BuiltSemantics H)
                                              (core.convert.FromSame
                                              r1_wire.Error) residual
                                          ok (r20, commitments2)
                                      | core.ops.control_flow.ControlFlow.Break
                                        residual =>
                                        let r19 ←
                                          core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
                                            (host_semantic.BuiltSemantics H)
                                            (core.convert.FromSame
                                            r1_wire.Error) residual
                                        ok (r19, commitments2)
                                    | core.ops.control_flow.ControlFlow.Break
                                      residual =>
                                      let r18 ←
                                        core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
                                          (host_semantic.BuiltSemantics H)
                                          (core.convert.FromSame r1_wire.Error)
                                          residual
                                      ok (r18, commitments2)
                                  | core.ops.control_flow.ControlFlow.Break
                                    residual =>
                                    let r17 ←
                                      core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
                                        (host_semantic.BuiltSemantics H)
                                        (core.convert.FromSame r1_wire.Error)
                                        residual
                                    ok (r17, commitments2)
                                | core.ops.control_flow.ControlFlow.Break
                                  residual =>
                                  let r16 ←
                                    core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
                                      (host_semantic.BuiltSemantics H)
                                      (core.convert.FromSame r1_wire.Error)
                                      residual
                                  ok (r16, commitments2)
                              | core.ops.control_flow.ControlFlow.Break
                                residual =>
                                let r15 ←
                                  core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
                                    (host_semantic.BuiltSemantics H)
                                    (core.convert.FromSame r1_wire.Error)
                                    residual
                                ok (r15, commitments2)
                            | core.ops.control_flow.ControlFlow.Break residual
                              =>
                              let r14 ←
                                core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
                                  (host_semantic.BuiltSemantics H)
                                  (core.convert.FromSame r1_wire.Error)
                                  residual
                              ok (r14, commitments2)
                          | core.ops.control_flow.ControlFlow.Break residual =>
                            let r13 ←
                              core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
                                (host_semantic.BuiltSemantics H)
                                (core.convert.FromSame r1_wire.Error) residual
                            ok (r13, commitments2)
                        | core.ops.control_flow.ControlFlow.Break residual =>
                          let r12 ←
                            core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
                              (host_semantic.BuiltSemantics H)
                              (core.convert.FromSame r1_wire.Error) residual
                          ok (r12, commitments2)
                      | core.ops.control_flow.ControlFlow.Break residual =>
                        let r11 ←
                          core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
                            (host_semantic.BuiltSemantics H)
                            (core.convert.FromSame r1_wire.Error) residual
                        ok (r11, commitments2)
                | core.ops.control_flow.ControlFlow.Break residual =>
                  let r10 ←
                    core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
                      (host_semantic.BuiltSemantics H) (core.convert.FromSame
                      r1_wire.Error) residual
                  ok (r10, commitments1)
              | core.ops.control_flow.ControlFlow.Break residual =>
                let r8 ←
                  core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
                    (host_semantic.BuiltSemantics H) (core.convert.FromSame
                    r1_wire.Error) residual
                ok (r8, commitments1)
            | core.ops.control_flow.ControlFlow.Break residual =>
              let r7 ←
                core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
                  (host_semantic.BuiltSemantics H) (core.convert.FromSame
                  r1_wire.Error) residual
              ok (r7, commitments1)
          | core.ops.control_flow.ControlFlow.Break residual =>
            let r6 ←
              core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
                (host_semantic.BuiltSemantics H) (core.convert.FromSame
                r1_wire.Error) residual
            ok (r6, commitments1)
        | core.ops.control_flow.ControlFlow.Break residual =>
          let r5 ←
            core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
              (host_semantic.BuiltSemantics H) (core.convert.FromSame
              r1_wire.Error) residual
          ok (r5, commitments1)
      | core.ops.control_flow.ControlFlow.Break residual =>
        let r4 ←
          core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
            (host_semantic.BuiltSemantics H) (core.convert.FromSame
            r1_wire.Error) residual
        ok (r4, commitments1)
    | core.ops.control_flow.ControlFlow.Break residual =>
      let r2 ←
        core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
          (host_semantic.BuiltSemantics H) (core.convert.FromSame
          r1_wire.Error) residual
      ok (r2, commitments1)
  | core.ops.control_flow.ControlFlow.Break residual =>
    let r1 ←
      core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
        (host_semantic.BuiltSemantics H) (core.convert.FromSame r1_wire.Error)
        residual
    ok (r1, commitments)


end R1Z.PV_RE_ComposedSuffix5_055
pv_composed5_source_contexts ProverRwFull.host_semantic.build_with_helper_mode
pv_composed5_source_contexts R1Z.PV_RE_ComposedSuffix5_055.continueAfter

set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RE_ComposedSuffix5_056
open Aeneas Aeneas.Std Result ControlFlow Error ProverRwFull
variable [ExternalTypes] [ExternalFuns]
private abbrev Payload {α : Type} (_ : Result α) := α

/-- The actual entire suffix after the first bind in `host_semantic.check_secure_column`.
Recursive calls remain the original extracted calls. -/
def continueAfter (column : Array aspis_core.field.QM31 1024#usize) (out : Payload (host_semantic.check_secure_column_loop column 0#usize)) : Result (core.result.Result Unit r1_wire.Error) := do
  let pending_return := out
  match pending_return with
  | none => ok (core.result.Result.Ok ())
  | some r => ok r


end R1Z.PV_RE_ComposedSuffix5_056
pv_composed5_source_contexts ProverRwFull.host_semantic.check_secure_column
pv_composed5_source_contexts R1Z.PV_RE_ComposedSuffix5_056.continueAfter

set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RE_ComposedSuffix5_057
open Aeneas Aeneas.Std Result ControlFlow Error ProverRwFull
variable [ExternalTypes] [ExternalFuns]
private abbrev Payload {α : Type} (_ : Result α) := α

/-- The actual entire suffix after the first bind in `host_semantic.initial_mask_value`.
Recursive calls remain the original extracted calls. -/
def continueAfter (columns : Array (alloc.vec.Vec aspis_core.field.QM31) 29#usize) (row : Std.Usize) (out : Payload (host_semantic.boolean_point row)) : Result aspis_core.field.QM31 := do
  let point := out
  let q ← aspis_core.field.QM31.ZERO
  let semantic := Array.repeat 16#usize q
  let mask_only := Array.repeat 10#usize q
  let semantic1 ←
    host_semantic.initial_mask_value_loop0 columns row semantic 0#usize
  let mask_only1 ←
    host_semantic.initial_mask_value_loop1 columns row mask_only 0#usize
  let v ← Array.index_usize columns 27#usize
  let q1 ←
    alloc.vec.Vec.index (core.slice.index.SliceIndexUsizeSlice
      aspis_core.field.QM31) v row
  aspis_core.state_only_hiding.state_only_selected_mask_value semantic1
    mask_only1 q1 point


end R1Z.PV_RE_ComposedSuffix5_057
pv_composed5_source_contexts ProverRwFull.host_semantic.initial_mask_value
pv_composed5_source_contexts R1Z.PV_RE_ComposedSuffix5_057.continueAfter

set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RE_ComposedSuffix5_058
open Aeneas Aeneas.Std Result ControlFlow Error ProverRwFull
variable [ExternalTypes] [ExternalFuns]
private abbrev Payload {α : Type} (_ : Result α) := α

/-- The actual entire suffix after the first bind in `host_semantic.no_pole`.
Recursive calls remain the original extracted calls. -/
def continueAfter (compiled :
  aspis_statement.pool_v1.pair_forest_trace.PoolV1PairForestMergedC1CompilationV1) (lambda : aspis_core.field.QM31) (chi : aspis_core.field.QM31) (out : Payload (host_semantic.lean_copy_row_values compiled.trace lambda)) : Result (core.result.Result Bool r1_wire.Error) := do
  let r := out
  let cf ← core.result.Result.Insts.CoreOpsTry.branch r
  match cf with
  | core.ops.control_flow.ControlFlow.Continue val =>
    let r1 ←
      aspis_statement.pool_v1.pair_forest_hiding.pool_v1_pair_forest_copy_active_row_masks_v1
    let r2 ←
      core.result.Result.map_err
        host_semantic.no_pole.closure.Insts.CoreOpsFunctionFnOnceTuplePoolV1PairHidingLayoutErrorV1Error
        r1 ()
    let cf1 ← core.result.Result.Insts.CoreOpsTry.branch r2
    match cf1 with
    | core.ops.control_flow.ControlFlow.Continue val1 =>
      let s := alloc.vec.Vec.deref val
      let b ← ct_pole.all_slots_clear s val1 chi
      ok (core.result.Result.Ok b)
    | core.ops.control_flow.ControlFlow.Break residual =>
      core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
        Bool (core.convert.FromSame r1_wire.Error) residual
  | core.ops.control_flow.ControlFlow.Break residual =>
    core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
      Bool (core.convert.FromSame r1_wire.Error) residual


end R1Z.PV_RE_ComposedSuffix5_058
pv_composed5_source_contexts ProverRwFull.host_semantic.no_pole
pv_composed5_source_contexts R1Z.PV_RE_ComposedSuffix5_058.continueAfter

set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RE_ComposedSuffix5_059
open Aeneas Aeneas.Std Result ControlFlow Error ProverRwFull
variable [ExternalTypes] [ExternalFuns]
private abbrev Payload {α : Type} (_ : Result α) := α

/-- The actual entire suffix after the first bind in `host_semantic.point_claims`.
Recursive calls remain the original extracted calls. -/
def continueAfter (columns : Array (alloc.vec.Vec aspis_core.field.QM31) 29#usize) (point : Array aspis_core.field.QM31 10#usize) (out : Payload (r1_wire.statement_points point)) : Result (core.result.Result (Array (Array aspis_core.field.QM31 29#usize)
    3#usize) r1_wire.Error) := do
  let points := out
  let a ← Array.index_usize points 0#usize
  let r ← host_semantic.claims_at_point columns a
  let cf ← core.result.Result.Insts.CoreOpsTry.branch r
  match cf with
  | core.ops.control_flow.ControlFlow.Continue val =>
    let a1 ← Array.index_usize points 1#usize
    let r1 ← host_semantic.claims_at_point columns a1
    let cf1 ← core.result.Result.Insts.CoreOpsTry.branch r1
    match cf1 with
    | core.ops.control_flow.ControlFlow.Continue val1 =>
      let a2 ← Array.index_usize points 2#usize
      let r2 ← host_semantic.claims_at_point columns a2
      let cf2 ← core.result.Result.Insts.CoreOpsTry.branch r2
      match cf2 with
      | core.ops.control_flow.ControlFlow.Continue val2 =>
        ok (core.result.Result.Ok (Array.make 3#usize [ val, val1, val2 ]))
      | core.ops.control_flow.ControlFlow.Break residual =>
        core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
          (Array (Array aspis_core.field.QM31 29#usize) 3#usize)
          (core.convert.FromSame r1_wire.Error) residual
    | core.ops.control_flow.ControlFlow.Break residual =>
      core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
        (Array (Array aspis_core.field.QM31 29#usize) 3#usize)
        (core.convert.FromSame r1_wire.Error) residual
  | core.ops.control_flow.ControlFlow.Break residual =>
    core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
      (Array (Array aspis_core.field.QM31 29#usize) 3#usize)
      (core.convert.FromSame r1_wire.Error) residual


end R1Z.PV_RE_ComposedSuffix5_059
pv_composed5_source_contexts ProverRwFull.host_semantic.point_claims
pv_composed5_source_contexts R1Z.PV_RE_ComposedSuffix5_059.continueAfter

set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RE_ComposedSuffix5_060
open Aeneas Aeneas.Std Result ControlFlow Error ProverRwFull
variable [ExternalTypes] [ExternalFuns]
private abbrev Payload {α : Type} (_ : Result α) := α

/-- The actual entire suffix after the first bind in `host_semantic.semantic_row`.
Recursive calls remain the original extracted calls. -/
def continueAfter {H : Type} (aspis_coredigestDigest32Inst : aspis_core.digest.Digest32 H) (row : Std.U8) (payload : Slice Std.U8) (transcript : host_wire.SemanticTranscript H) (bytes : alloc.vec.Vec Std.U8) (out : Payload (host_wire.record row payload)) : Result ((core.result.Result aspis_core.field.QM31 r1_wire.Error) ×
    (host_wire.SemanticTranscript H) × (alloc.vec.Vec Std.U8)) := do
  let r := out
  let cf ← core.result.Result.Insts.CoreOpsTry.branch r
  match cf with
  | core.ops.control_flow.ControlFlow.Continue val =>
    let s := alloc.vec.Vec.deref val
    let (r1, transcript1) ←
      host_wire.SemanticTranscript.semantic aspis_coredigestDigest32Inst
        transcript row s
    let cf1 ← core.result.Result.Insts.CoreOpsTry.branch r1
    match cf1 with
    | core.ops.control_flow.ControlFlow.Continue val1 =>
      let s1 := alloc.vec.Vec.deref val
      let bytes1 ←
        alloc.vec.Vec.extend_from_slice core.clone.CloneU8 bytes s1
      ok (core.result.Result.Ok val1, transcript1, bytes1)
    | core.ops.control_flow.ControlFlow.Break residual =>
      let r2 ←
        core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
          aspis_core.field.QM31 (core.convert.FromSame r1_wire.Error) residual
      ok (r2, transcript1, bytes)
  | core.ops.control_flow.ControlFlow.Break residual =>
    let r1 ←
      core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
        aspis_core.field.QM31 (core.convert.FromSame r1_wire.Error) residual
    ok (r1, transcript, bytes)


end R1Z.PV_RE_ComposedSuffix5_060
pv_composed5_source_contexts ProverRwFull.host_semantic.semantic_row
pv_composed5_source_contexts R1Z.PV_RE_ComposedSuffix5_060.continueAfter

set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RE_ComposedSuffix5_061
open Aeneas Aeneas.Std Result ControlFlow Error ProverRwFull
variable [ExternalTypes] [ExternalFuns]
private abbrev Payload {α : Type} (_ : Result α) := α

/-- The actual entire suffix after the first bind in `host_sumcheck.interpolation_basis_cell`.
Recursive calls remain the original extracted calls. -/
def continueAfter (basis : Array aspis_core.field.M31 28#usize) (k : Std.Usize) (j : Std.Usize) (out : Payload (host_sumcheck.interpolation_shift basis k)) : Result (Array aspis_core.field.M31 28#usize) := do
  let shifted := out
  let m ← Array.index_usize basis k
  let i ← Aeneas.Std.lift (UScalar.cast .U32 j)
  let m1 ← aspis_core.field.M31.mul m i
  let next ← aspis_core.field.M31.sub shifted m1
  Array.update basis k next


end R1Z.PV_RE_ComposedSuffix5_061
pv_composed5_source_contexts ProverRwFull.host_sumcheck.interpolation_basis_cell
pv_composed5_source_contexts R1Z.PV_RE_ComposedSuffix5_061.continueAfter

set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RE_ComposedSuffix5_062
open Aeneas Aeneas.Std Result ControlFlow Error ProverRwFull
variable [ExternalTypes] [ExternalFuns]
private abbrev Payload {α : Type} (_ : Result α) := α

/-- The actual entire suffix after the first bind in `host_sumcheck.prove_sumcheck_round.closure.Insts.CoreOpsFunctionFnMutTupleUsizeResultQM31Error.call_mut`.
Recursive calls remain the original extracted calls. -/
def continueAfter {H : Type} {F : Type} (aspis_coredigestDigest32Inst :
  aspis_core.digest.Digest32 H) (OracleInst : host_sumcheck.Oracle F) (state : host_sumcheck.prove_sumcheck_round.closure H F) (args : Std.Usize) (out : Payload (host_sumcheck.prove_sumcheck_round.closure.Insts.CoreOpsFunctionFnTupleUsizeResultQM31Error.call
      aspis_coredigestDigest32Inst OracleInst state args)) : Result ((core.result.Result aspis_core.field.QM31 r1_wire.Error) ×
    (host_sumcheck.prove_sumcheck_round.closure H F)) := do
  let r := out
  ok (r, state)


end R1Z.PV_RE_ComposedSuffix5_062
pv_composed5_source_contexts ProverRwFull.host_sumcheck.prove_sumcheck_round.closure.Insts.CoreOpsFunctionFnMutTupleUsizeResultQM31Error.call_mut
pv_composed5_source_contexts R1Z.PV_RE_ComposedSuffix5_062.continueAfter

set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RE_ComposedSuffix5_063
open Aeneas Aeneas.Std Result ControlFlow Error ProverRwFull
variable [ExternalTypes] [ExternalFuns]
private abbrev Payload {α : Type} (_ : Result α) := α

/-- The actual entire suffix after the first bind in `host_sumcheck.prove_sumcheck_round.closure.Insts.CoreOpsFunctionFnOnceTupleUsizeResultQM31Error.call_once`.
Recursive calls remain the original extracted calls. -/
def continueAfter {H : Type} {F : Type} (aspis_coredigestDigest32Inst :
  aspis_core.digest.Digest32 H) (OracleInst : host_sumcheck.Oracle F) (c : host_sumcheck.prove_sumcheck_round.closure H F) (i : Std.Usize) (out : Payload (host_sumcheck.prove_sumcheck_round.closure.Insts.CoreOpsFunctionFnMutTupleUsizeResultQM31Error.call_mut
      aspis_coredigestDigest32Inst OracleInst c i)) : Result (core.result.Result aspis_core.field.QM31 r1_wire.Error) := do
  let (r, _) := out
  ok r


end R1Z.PV_RE_ComposedSuffix5_063
pv_composed5_source_contexts ProverRwFull.host_sumcheck.prove_sumcheck_round.closure.Insts.CoreOpsFunctionFnOnceTupleUsizeResultQM31Error.call_once
pv_composed5_source_contexts R1Z.PV_RE_ComposedSuffix5_063.continueAfter

set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RE_ComposedSuffix5_064
open Aeneas Aeneas.Std Result ControlFlow Error ProverRwFull
variable [ExternalTypes] [ExternalFuns]
private abbrev Payload {α : Type} (_ : Result α) := α

/-- The actual entire suffix after the first bind in `host_tree.node_count`.
Recursive calls remain the original extracted calls. -/
def continueAfter (indices : Slice Std.U32) (out : Payload (host_tree.check_indices indices)) : Result (Option Std.Usize) := do
  let o := out
  let cf ← core.option.Option.Insts.CoreOpsTry_traitTry.branch o
  match cf with
  | core.ops.control_flow.ControlFlow.Continue _ =>
    let level := Array.repeat 16#usize 0#u32
    let i := Slice.len indices
    let (s, index_mut_back) ←
      core.array.Array.index_mut (core.ops.index.IndexMutSlice
        (core.slice.index.SliceIndexRangeToUsizeSlice Std.U32)) level
        { «end» := i }
    let s1 ← core.slice.Slice.copy_from_slice core.marker.CopyU32 s indices
    let level1 := index_mut_back s1
    let i1 := Slice.len indices
    let i2 ← multiproof.LEAF_BITS
    let i3 ← host_tree.count_levels level1 i1 0#u32 0#usize i2
    ok (some i3)
  | core.ops.control_flow.ControlFlow.Break residual =>
    core.option.Option.Insts.CoreOpsTry_traitFromResidualOptionInfallible.from_residual
      Std.Usize residual


end R1Z.PV_RE_ComposedSuffix5_064
pv_composed5_source_contexts ProverRwFull.host_tree.node_count
pv_composed5_source_contexts R1Z.PV_RE_ComposedSuffix5_064.continueAfter

set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RE_ComposedSuffix5_065
open Aeneas Aeneas.Std Result ControlFlow Error ProverRwFull
variable [ExternalTypes] [ExternalFuns]
private abbrev Payload {α : Type} (_ : Result α) := α

/-- The actual entire suffix after the first bind in `host_wire.parse_record`.
Recursive calls remain the original extracted calls. -/
def continueAfter (row : Std.U8) (record1 : Slice Std.U8) (out : Payload (r1_wire.row_shape row)) : Result (core.result.Result (Slice Std.U8) r1_wire.Error) := do
  let o := out
  let r ← core.option.Option.ok_or o r1_wire.Error.InvalidRow
  let cf ← core.result.Result.Insts.CoreOpsTry.branch r
  match cf with
  | core.ops.control_flow.ControlFlow.Continue val =>
    let (tag, size) := val
    let i := Slice.len record1
    let i1 ← Aeneas.Std.lift (Std.Usize.wrapping_add 5#usize size)
    if i != i1
    then ok (core.result.Result.Err (r1_wire.Error.Length row))
    else
      let i2 ← Slice.index_usize record1 0#usize
      if i2 != tag
      then ok (core.result.Result.Err (r1_wire.Error.Tag row))
      else
        let i3 ← Slice.index_usize record1 1#usize
        let i4 ← Slice.index_usize record1 2#usize
        let i5 ← Slice.index_usize record1 3#usize
        let i6 ← Slice.index_usize record1 4#usize
        let i7 ←
          Aeneas.Std.lift (core.num.U32.from_le_bytes
            (Array.make 4#usize [ i3, i4, i5, i6 ]))
        let i8 ← Aeneas.Std.lift (UScalar.cast .Usize i7)
        if i8 != size
        then ok (core.result.Result.Err (r1_wire.Error.Length row))
        else
          let payload ←
            core.slice.index.Slice.index
              (core.slice.index.SliceIndexRangeFromUsizeSlice Std.U8) record1
              { start := 5#usize }
          if row >= 14#u8
          then
            let r1 ← host_wire.validate_record_fields row payload
            let cf1 ← core.result.Result.Insts.CoreOpsTry.branch r1
            match cf1 with
            | core.ops.control_flow.ControlFlow.Continue _ =>
              ok (core.result.Result.Ok payload)
            | core.ops.control_flow.ControlFlow.Break residual =>
              core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
                (Slice Std.U8) (core.convert.FromSame r1_wire.Error) residual
          else ok (core.result.Result.Ok payload)
  | core.ops.control_flow.ControlFlow.Break residual =>
    core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
      (Slice Std.U8) (core.convert.FromSame r1_wire.Error) residual


end R1Z.PV_RE_ComposedSuffix5_065
pv_composed5_source_contexts ProverRwFull.host_wire.parse_record
pv_composed5_source_contexts R1Z.PV_RE_ComposedSuffix5_065.continueAfter

set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RE_ComposedSuffix5_066
open Aeneas Aeneas.Std Result ControlFlow Error ProverRwFull
variable [ExternalTypes] [ExternalFuns]
private abbrev Payload {α : Type} (_ : Result α) := α

/-- The actual entire suffix after the first bind in `host_wire.record`.
Recursive calls remain the original extracted calls. -/
def continueAfter (row : Std.U8) (payload : Slice Std.U8) (out : Payload (r1_wire.row_shape row)) : Result (core.result.Result (alloc.vec.Vec Std.U8) r1_wire.Error) := do
  let o := out
  let r ← core.option.Option.ok_or o r1_wire.Error.InvalidRow
  let cf ← core.result.Result.Insts.CoreOpsTry.branch r
  match cf with
  | core.ops.control_flow.ControlFlow.Continue val =>
    let (tag, size) := val
    let i := Slice.len payload
    if i != size
    then ok (core.result.Result.Err (r1_wire.Error.Length row))
    else
      let i1 ← Aeneas.Std.lift (Std.Usize.wrapping_add 5#usize size)
      let out := alloc.vec.Vec.with_capacity Std.U8 i1
      let out1 ← alloc.vec.Vec.push out tag
      let i2 ← Aeneas.Std.lift (UScalar.cast .U32 size)
      let a ← Aeneas.Std.lift (core.num.U32.to_le_bytes i2)
      let s ← Aeneas.Std.lift (Array.to_slice a)
      let out2 ← alloc.vec.Vec.extend_from_slice core.clone.CloneU8 out1 s
      let out3 ←
        alloc.vec.Vec.extend_from_slice core.clone.CloneU8 out2 payload
      let s1 := alloc.vec.Vec.deref out3
      let r1 ← host_wire.parse_record row s1
      let cf1 ← core.result.Result.Insts.CoreOpsTry.branch r1
      match cf1 with
      | core.ops.control_flow.ControlFlow.Continue _ =>
        ok (core.result.Result.Ok out3)
      | core.ops.control_flow.ControlFlow.Break residual =>
        core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
          (alloc.vec.Vec Std.U8) (core.convert.FromSame r1_wire.Error) residual
  | core.ops.control_flow.ControlFlow.Break residual =>
    core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
      (alloc.vec.Vec Std.U8) (core.convert.FromSame r1_wire.Error) residual


end R1Z.PV_RE_ComposedSuffix5_066
pv_composed5_source_contexts ProverRwFull.host_wire.record
pv_composed5_source_contexts R1Z.PV_RE_ComposedSuffix5_066.continueAfter

set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RE_ComposedSuffix5_067
open Aeneas Aeneas.Std Result ControlFlow Error ProverRwFull
variable [ExternalTypes] [ExternalFuns]
private abbrev Payload {α : Type} (_ : Result α) := α

/-- The actual entire suffix after the first bind in `prover.Backend.Insts.Aspis_r1_cost_probeHost_semanticCommitments.c1`.
Recursive calls remain the original extracted calls. -/
def continueAfter (self : prover.Backend) (columns : Array (alloc.vec.Vec aspis_core.field.M31) 26#usize) (d : Array aspis_core.field.QM31 1024#usize) (out : Payload (prover.Backend.Insts.Aspis_r1_cost_probeHost_semanticCommitments.c1_loop0
      self columns 0#usize)) : Result ((core.result.Result (Array Std.U8 32#usize) r1_wire.Error) ×
    prover.Backend) := do
  let self1 := out
  let self2 ←
    prover.Backend.Insts.Aspis_r1_cost_probeHost_semanticCommitments.c1_loop1
      self1 d 0#usize
  let (o, o1) := core.option.Option.take self2.c1_salts
  let r ← core.option.Option.ok_or o r1_wire.Error.Public
  let cf ← core.result.Result.Insts.CoreOpsTry.branch r
  match cf with
  | core.ops.control_flow.ControlFlow.Continue val =>
    let s := alloc.vec.Vec.deref self2.messages
    let r1 ←
      host_commitment.Commitment.new_salted self2.hash self2.domain
        host_commitment.CommitmentTime.C1 s self2.variant val
    let r2 ←
      core.result.Result.map_err
        prover.CommitmentsBackend.c1.closure.Insts.CoreOpsFunctionFnOnceTupleErrorError
        r1 ()
    let cf1 ← core.result.Result.Insts.CoreOpsTry.branch r2
    match cf1 with
    | core.ops.control_flow.ControlFlow.Continue val1 =>
      let root ← host_commitment.Commitment.root val1
      ok (core.result.Result.Ok root,
        { self2 with c1 := (some val1), c1_salts := o1 })
    | core.ops.control_flow.ControlFlow.Break residual =>
      let r3 ←
        core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
          (Array Std.U8 32#usize) (core.convert.FromSame r1_wire.Error)
          residual
      ok (r3, { self2 with c1_salts := o1 })
  | core.ops.control_flow.ControlFlow.Break residual =>
    let r1 ←
      core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
        (Array Std.U8 32#usize) (core.convert.FromSame r1_wire.Error) residual
    ok (r1, { self2 with c1_salts := o1 })


end R1Z.PV_RE_ComposedSuffix5_067
pv_composed5_source_contexts ProverRwFull.prover.Backend.Insts.Aspis_r1_cost_probeHost_semanticCommitments.c1
pv_composed5_source_contexts R1Z.PV_RE_ComposedSuffix5_067.continueAfter

set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RE_ComposedSuffix5_068
open Aeneas Aeneas.Std Result ControlFlow Error ProverRwFull
variable [ExternalTypes] [ExternalFuns]
private abbrev Payload {α : Type} (_ : Result α) := α

/-- The actual entire suffix after the first bind in `prover.Backend.Insts.Aspis_r1_cost_probeHost_semanticCommitments.c2`.
Recursive calls remain the original extracted calls. -/
def continueAfter (self : prover.Backend) (h1 : Slice aspis_core.field.QM31) (g : Array aspis_core.field.QM31 1024#usize) (out : Payload (prover.Backend.Insts.Aspis_r1_cost_probeHost_semanticCommitments.c2_loop0
      self h1 0#usize)) : Result ((core.result.Result (Array Std.U8 32#usize) r1_wire.Error) ×
    prover.Backend) := do
  let self1 := out
  let self2 ←
    prover.Backend.Insts.Aspis_r1_cost_probeHost_semanticCommitments.c2_loop1
      self1 g 0#usize
  let (o, o1) := core.option.Option.take self2.c2_salts
  let r ← core.option.Option.ok_or o r1_wire.Error.Public
  let cf ← core.result.Result.Insts.CoreOpsTry.branch r
  match cf with
  | core.ops.control_flow.ControlFlow.Continue val =>
    let s := alloc.vec.Vec.deref self2.messages
    let r1 ←
      host_commitment.Commitment.new_salted self2.hash self2.domain
        host_commitment.CommitmentTime.C2 s self2.variant val
    let r2 ←
      core.result.Result.map_err
        prover.CommitmentsBackend.c2.closure.Insts.CoreOpsFunctionFnOnceTupleErrorError
        r1 ()
    let cf1 ← core.result.Result.Insts.CoreOpsTry.branch r2
    match cf1 with
    | core.ops.control_flow.ControlFlow.Continue val1 =>
      let root ← host_commitment.Commitment.root val1
      ok (core.result.Result.Ok root,
        { self2 with c2 := (some val1), c2_salts := o1 })
    | core.ops.control_flow.ControlFlow.Break residual =>
      let r3 ←
        core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
          (Array Std.U8 32#usize) (core.convert.FromSame r1_wire.Error)
          residual
      ok (r3, { self2 with c2_salts := o1 })
  | core.ops.control_flow.ControlFlow.Break residual =>
    let r1 ←
      core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
        (Array Std.U8 32#usize) (core.convert.FromSame r1_wire.Error) residual
    ok (r1, { self2 with c2_salts := o1 })


end R1Z.PV_RE_ComposedSuffix5_068
pv_composed5_source_contexts ProverRwFull.prover.Backend.Insts.Aspis_r1_cost_probeHost_semanticCommitments.c2
pv_composed5_source_contexts R1Z.PV_RE_ComposedSuffix5_068.continueAfter

set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RE_ComposedSuffix5_069
open Aeneas Aeneas.Std Result ControlFlow Error ProverRwFull
variable [ExternalTypes] [ExternalFuns]
private abbrev Payload {α : Type} (_ : Result α) := α

/-- The actual entire suffix after the first bind in `prover.append_node_slots`.
Recursive calls remain the original extracted calls. -/
def continueAfter (out : alloc.vec.Vec Std.U8) (cc1 : host_commitment.Commitment) (cc2 : host_commitment.Commitment) (tree : host_tree.BinaryTree) (queries : Array Std.U32 22#usize) (pvBoundValue : Payload (prover.append_node_slot out cc1 cc2 tree queries 0#usize 0#usize)) : Result (core.result.Result (alloc.vec.Vec Std.U8) verifier.Error) := do
  let r := pvBoundValue
  let cf ← core.result.Result.Insts.CoreOpsTry.branch r
  match cf with
  | core.ops.control_flow.ControlFlow.Continue val =>
    let r1 ← prover.append_node_slot val cc1 cc2 tree queries 0#usize 1#usize
    let cf1 ← core.result.Result.Insts.CoreOpsTry.branch r1
    match cf1 with
    | core.ops.control_flow.ControlFlow.Continue val1 =>
      let r2 ←
        prover.append_node_slot val1 cc1 cc2 tree queries 0#usize 2#usize
      let cf2 ← core.result.Result.Insts.CoreOpsTry.branch r2
      match cf2 with
      | core.ops.control_flow.ControlFlow.Continue val2 =>
        let r3 ←
          prover.append_node_slot val2 cc1 cc2 tree queries 1#usize 0#usize
        let cf3 ← core.result.Result.Insts.CoreOpsTry.branch r3
        match cf3 with
        | core.ops.control_flow.ControlFlow.Continue val3 =>
          let r4 ←
            prover.append_node_slot val3 cc1 cc2 tree queries 1#usize 1#usize
          let cf4 ← core.result.Result.Insts.CoreOpsTry.branch r4
          match cf4 with
          | core.ops.control_flow.ControlFlow.Continue val4 =>
            prover.append_node_slot val4 cc1 cc2 tree queries 1#usize 2#usize
          | core.ops.control_flow.ControlFlow.Break residual =>
            core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
              (alloc.vec.Vec Std.U8) (core.convert.FromSame verifier.Error)
              residual
        | core.ops.control_flow.ControlFlow.Break residual =>
          core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
            (alloc.vec.Vec Std.U8) (core.convert.FromSame verifier.Error)
            residual
      | core.ops.control_flow.ControlFlow.Break residual =>
        core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
          (alloc.vec.Vec Std.U8) (core.convert.FromSame verifier.Error)
          residual
    | core.ops.control_flow.ControlFlow.Break residual =>
      core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
        (alloc.vec.Vec Std.U8) (core.convert.FromSame verifier.Error) residual
  | core.ops.control_flow.ControlFlow.Break residual =>
    core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
      (alloc.vec.Vec Std.U8) (core.convert.FromSame verifier.Error) residual


end R1Z.PV_RE_ComposedSuffix5_069
pv_composed5_source_contexts ProverRwFull.prover.append_node_slots
pv_composed5_source_contexts R1Z.PV_RE_ComposedSuffix5_069.continueAfter

set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RE_ComposedSuffix5_070
open Aeneas Aeneas.Std Result ControlFlow Error ProverRwFull
variable [ExternalTypes] [ExternalFuns]
private abbrev Payload {α : Type} (_ : Result α) := α

/-- The actual entire suffix after the first bind in `prover.append_opening_base_row`.
Recursive calls remain the original extracted calls. -/
def continueAfter (out : alloc.vec.Vec Std.U8) (row : Array aspis_core.field.wide_exact.WideExact 29#usize) (pvBoundValue : Payload (prover.append_opening_base_row_loop out row 0#usize)) : Result (alloc.vec.Vec Std.U8) := do
  let out1 := pvBoundValue
  let we ← Array.index_usize row 28#usize
  let bytes ← aspis_core.field.wide_exact.WideExact.to_le_bytes we
  let s ←
    core.array.Array.index (core.ops.index.IndexSlice
      (core.slice.index.SliceIndexRangeToUsizeSlice Std.U8)) bytes
      { «end» := 16#usize }
  alloc.vec.Vec.extend_from_slice core.clone.CloneU8 out1 s


end R1Z.PV_RE_ComposedSuffix5_070
pv_composed5_source_contexts ProverRwFull.prover.append_opening_base_row
pv_composed5_source_contexts R1Z.PV_RE_ComposedSuffix5_070.continueAfter

set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RE_ComposedSuffix5_071
open Aeneas Aeneas.Std Result ControlFlow Error ProverRwFull
variable [ExternalTypes] [ExternalFuns]
private abbrev Payload {α : Type} (_ : Result α) := α

/-- The actual entire suffix after the first bind in `prover.audit_masks`.
Recursive calls remain the original extracted calls. -/
def continueAfter (c1 : Slice (alloc.vec.Vec aspis_core.field.M31)) (mask_only : Array (alloc.vec.Vec aspis_core.field.M31) 10#usize) (d : Array aspis_core.field.QM31 1024#usize) (g : Array aspis_core.field.QM31 1024#usize) (h1_padding : Array aspis_core.field.QM31 1024#usize) (masks : Array Std.U16 64#usize) (out : Payload (prover.audit_masks_loop0 c1 masks 0#usize 0#usize)) : Result prover.MaskedFixtureAudit := do
  let c1_columns_inactive_balanced := out
  let mask_only_columns_inactive_balanced ←
    prover.audit_masks_loop1 mask_only masks 0#usize 0#usize
  let s ← Aeneas.Std.lift (Array.to_slice d)
  let q ← prover.inactive_sum_k s masks
  let q1 ← aspis_core.field.QM31.ZERO
  let b ← aspis_core.field.QM31.Insts.CoreCmpPartialEqQM31.eq q q1
  let s1 ← Aeneas.Std.lift (Array.to_slice g)
  let q2 ← prover.inactive_sum_k s1 masks
  let b1 ← aspis_core.field.QM31.Insts.CoreCmpPartialEqQM31.eq q2 q1
  let s2 ← Aeneas.Std.lift (Array.to_slice h1_padding)
  let q3 ← prover.inactive_sum_k s2 masks
  let b2 ← aspis_core.field.QM31.Insts.CoreCmpPartialEqQM31.eq q3 q1
  ok
    {
      c1_columns_inactive_balanced,
      mask_only_columns_inactive_balanced,
      d_inactive_balanced := b,
      g_inactive_balanced := b1,
      h1_padding_inactive_balanced := b2,
      h1_total_balanced := true
    }


end R1Z.PV_RE_ComposedSuffix5_071
pv_composed5_source_contexts ProverRwFull.prover.audit_masks
pv_composed5_source_contexts R1Z.PV_RE_ComposedSuffix5_071.continueAfter

set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RE_ComposedSuffix5_072
open Aeneas Aeneas.Std Result ControlFlow Error ProverRwFull
variable [ExternalTypes] [ExternalFuns]
private abbrev Payload {α : Type} (_ : Result α) := α

/-- The actual entire suffix after the first bind in `prover.derive_private_salt_step`.
Recursive calls remain the original extracted calls. -/
def continueAfter (reserved : aspis_prover.state_only_entropy.ReservedStateOnlyAttemptSecrets) (context : aspis_core.state_only_hiding.StateOnlyHidingContext) (hash : Slice (Slice Std.U8) → Result (Array Std.U8 32#usize)) (tag : Std.U8) (index : Std.U32) (salts : alloc.vec.Vec (Array Std.U8 32#usize)) (out : Payload (aspis_prover.state_only_entropy.ReservedStateOnlyAttemptSecrets.derive_pool_v1_leaf_salt
      reserved hash context tag index)) : Result (core.result.Result (alloc.vec.Vec (Array Std.U8 32#usize))
    verifier.Error) := do
  let r := out
  let r1 ←
    core.result.Result.map_err
      prover.derive_private_salt_step.closure.Insts.CoreOpsFunctionFnOnceTupleStateOnlyMaskBuildErrorError
      r ()
  let cf ← core.result.Result.Insts.CoreOpsTry.branch r1
  match cf with
  | core.ops.control_flow.ControlFlow.Continue val =>
    let salts1 ← alloc.vec.Vec.push salts val
    ok (core.result.Result.Ok salts1)
  | core.ops.control_flow.ControlFlow.Break residual =>
    core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
      (alloc.vec.Vec (Array Std.U8 32#usize)) (core.convert.FromSame
      verifier.Error) residual


end R1Z.PV_RE_ComposedSuffix5_072
pv_composed5_source_contexts ProverRwFull.prover.derive_private_salt_step
pv_composed5_source_contexts R1Z.PV_RE_ComposedSuffix5_072.continueAfter

set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RE_ComposedSuffix5_073
open Aeneas Aeneas.Std Result ControlFlow Error ProverRwFull
variable [ExternalTypes] [ExternalFuns]
private abbrev Payload {α : Type} (_ : Result α) := α

/-- The actual entire suffix after the first bind in `prover.prove_masked_with_attempt`.
Recursive calls remain the original extracted calls. -/
def continueAfter {T0 : Type} (aspis_proverstate_only_hidingStateOnlyMaskNonceStoreInst :
  aspis_prover.state_only_hiding.StateOnlyMaskNonceStore T0) (public1 : aspis_statement.pool_v1.pair_forest_semantic_terminal.r0.Public) (compiled :
  aspis_statement.pool_v1.pair_forest_trace.PoolV1PairForestMergedC1CompilationV1) (variant : transport.Variant) (hash : Slice (Slice Std.U8) → Result (Array Std.U8 32#usize)) (context : aspis_core.state_only_hiding.StateOnlyHidingContext) (binding : Array Std.U8 32#usize) (attempt : aspis_prover.state_only_entropy.StateOnlyAttemptSecrets) (nonce_store : T0) (out : Payload (aspis_prover.state_only_entropy.StateOnlyAttemptSecrets.reserve_and_build_pool_v1_pair_forest_mask_material_v1
      aspis_proverstate_only_hidingStateOnlyMaskNonceStoreInst attempt hash
      binding context nonce_store)) : Result ((core.result.Result ((alloc.vec.Vec Std.U8) ×
    prover.MaskedFixtureAudit) verifier.Error) × T0) := do
  let (r, nonce_store1) := out
  let r1 ←
    core.result.Result.map_err (BuiltinFnOnce
      aspis_prover.state_only_hiding.StateOnlyMaskBuildError verifier.Error) r
      (prover.mask_error)
  let cf ← core.result.Result.Insts.CoreOpsTry.branch r1
  match cf with
  | core.ops.control_flow.ControlFlow.Continue val =>
    let (reserved, material) := val
    let noised_c1 ←
      aspis_statement.state_only_trace.StateOnlyTraceFoundation.Insts.CoreCloneClone.clone
        compiled.semantic_c1
    let (r2, noised_c11) ←
      aspis_prover.state_only_hiding.apply_pool_v1_pair_forest_mask_material_v1
        noised_c1 material
    let r3 ←
      core.result.Result.map_err
        (prover.prove_masked_with_attempt.closure.Insts.CoreOpsFunctionFnOnceTupleStateOnlyMaskBuildErrorError
        aspis_proverstate_only_hidingStateOnlyMaskNonceStoreInst) r2 ()
    let cf1 ← core.result.Result.Insts.CoreOpsTry.branch r3
    match cf1 with
    | core.ops.control_flow.ControlFlow.Continue val1 =>
      let r4 ←
        aspis_statement.pool_v1.pair_forest_hiding.pool_v1_pair_forest_copy_active_row_masks_v1
      let r5 ←
        core.result.Result.map_err
          (prover.prove_masked_with_attempt.closure_1.Insts.CoreOpsFunctionFnOnceTuplePoolV1PairHidingLayoutErrorV1Error
          aspis_proverstate_only_hidingStateOnlyMaskNonceStoreInst) r4 ()
      let cf2 ← core.result.Result.Insts.CoreOpsTry.branch r5
      match cf2 with
      | core.ops.control_flow.ControlFlow.Continue val2 =>
        let r6 ←
          aspis_prover.state_only_entropy.ReservedStateOnlyAttemptSecrets.derive_pool_v1_pair_forest_zero_factor_d
            reserved hash context
        let r7 ←
          core.result.Result.map_err (BuiltinFnOnce
            aspis_prover.state_only_hiding.StateOnlyMaskBuildError
            verifier.Error) r6 (prover.mask_error)
        let cf3 ← core.result.Result.Insts.CoreOpsTry.branch r7
        match cf3 with
        | core.ops.control_flow.ControlFlow.Continue val3 =>
          let r8 ←
            Array.Insts.CoreConvertTryFromVecVec.try_from Global 1024#usize
              val3
          let r9 ←
            core.result.Result.map_err
              (prover.prove_masked_with_attempt.closure_2.Insts.CoreOpsFunctionFnOnceTupleVecQM31Error
              aspis_proverstate_only_hidingStateOnlyMaskNonceStoreInst) r8 ()
          let cf4 ← core.result.Result.Insts.CoreOpsTry.branch r9
          match cf4 with
          | core.ops.control_flow.ControlFlow.Continue val4 =>
            let i := alloc.vec.Vec.len val1.g
            if i != 1024#usize
            then
              ok (core.result.Result.Err verifier.Error.Semantic, nonce_store1)
            else
              let i1 := alloc.vec.Vec.len val1.h1_padding
              if i1 != 1024#usize
              then
                ok (core.result.Result.Err verifier.Error.Semantic,
                  nonce_store1)
              else
                let s := alloc.vec.Vec.deref val1.g
                let g ← prover.fixed_k_column s
                let s1 := alloc.vec.Vec.deref val1.h1_padding
                let h1_padding ← prover.fixed_k_column s1
                let s2 ← Aeneas.Std.lift (Array.to_slice noised_c11.c1)
                let audit ←
                  prover.audit_masks s2 val1.mask_only_c1 val4 g h1_padding
                    val2
                if audit.c1_columns_inactive_balanced != 16#usize
                then
                  ok (core.result.Result.Err verifier.Error.Semantic,
                    nonce_store1)
                else
                  if audit.mask_only_columns_inactive_balanced != 10#usize
                  then
                    ok (core.result.Result.Err verifier.Error.Semantic,
                      nonce_store1)
                  else
                    if audit.d_inactive_balanced
                    then
                      if audit.g_inactive_balanced
                      then
                        if audit.h1_padding_inactive_balanced
                        then
                          let i2 ← aspis_core.r0.merkle.C1_TAG
                          let r10 ←
                            prover.derive_private_salts reserved context hash
                              i2
                          let cf5 ←
                            core.result.Result.Insts.CoreOpsTry.branch r10
                          match cf5 with
                          | core.ops.control_flow.ControlFlow.Continue val5 =>
                            let i3 ← aspis_core.r0.merkle.C2_TAG
                            let r11 ←
                              prover.derive_private_salts reserved context hash
                                i3
                            let cf6 ←
                              core.result.Result.Insts.CoreOpsTry.branch r11
                            match cf6 with
                            | core.ops.control_flow.ControlFlow.Continue val6
                              =>
                              let r12 ← host_commitment.EncodingDomain.new
                              let r13 ←
                                core.result.Result.map_err
                                  (prover.prove_masked_with_attempt.closure_3.Insts.CoreOpsFunctionFnOnceTupleErrorError
                                  aspis_proverstate_only_hidingStateOnlyMaskNonceStoreInst)
                                  r12 ()
                              let cf7 ←
                                core.result.Result.Insts.CoreOpsTry.branch r13
                              match cf7 with
                              | core.ops.control_flow.ControlFlow.Continue val7
                                =>
                                let we ←
                                  aspis_core.field.wide_exact.WideExact.ZERO
                                let a := Array.repeat 1024#usize we
                                let v ←
                                  alloc.vec.from_elem (core.clone.CloneArray
                                    1024#usize
                                    aspis_core.field.wide_exact.WideExact.Insts.CoreCloneClone)
                                    a 29#usize
                                let (r14, backend) ←
                                  host_semantic.build_with_material
                                    aspis_core.digest.LegacyHashFn.Insts.Aspis_coreDigestDigest32
                                    prover.Backend.Insts.Aspis_r1_cost_probeHost_semanticCommitments
                                    public1 compiled noised_c11
                                    val1.mask_only_c1 val4 g h1_padding
                                    {
                                      hash,
                                      variant,
                                      domain := val7,
                                      messages := v,
                                      c1 := none,
                                      c2 := none,
                                      c1_salts := (some val5),
                                      c2_salts := (some val6)
                                    } hash variant
                                let r15 ←
                                  core.result.Result.map_err (BuiltinFnOnce
                                    r1_wire.Error verifier.Error) r14
                                    (prover.semantic_error)
                                let cf8 ←
                                  core.result.Result.Insts.CoreOpsTry.branch
                                    r15
                                match cf8 with
                                | core.ops.control_flow.ControlFlow.Continue
                                  val8 =>
                                  let v1 ←
                                    Array.index_usize val8.columns 26#usize
                                  let s3 := alloc.vec.Vec.deref v1
                                  let o ←
                                    aspis_statement.state_only_semantic.state_only_copy_helper_sum
                                      s3
                                  let q ← aspis_core.field.QM31.ZERO
                                  let h1_total_balanced ←
                                    core.option.Option.Insts.CoreCmpPartialEqOption.eq
                                      aspis_core.field.QM31.Insts.CoreCmpPartialEqQM31
                                      o (some q)
                                  if h1_total_balanced
                                  then
                                    let r16 ←
                                      prover.prove_from_semantics public1
                                        variant hash backend val8 (reserved,
                                        context)
                                    let cf9 ←
                                      core.result.Result.Insts.CoreOpsTry.branch
                                        r16
                                    match cf9 with
                                    |
                                      core.ops.control_flow.ControlFlow.Continue
                                      val9 =>
                                      ok (core.result.Result.Ok (val9,
                                        { audit with h1_total_balanced := true
                                        }), nonce_store1)
                                    | core.ops.control_flow.ControlFlow.Break
                                      residual =>
                                      let r17 ←
                                        core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
                                          ((alloc.vec.Vec Std.U8) ×
                                          prover.MaskedFixtureAudit)
                                          (core.convert.FromSame
                                          verifier.Error) residual
                                      ok (r17, nonce_store1)
                                  else
                                    ok (core.result.Result.Err
                                      verifier.Error.Semantic, nonce_store1)
                                | core.ops.control_flow.ControlFlow.Break
                                  residual =>
                                  let r16 ←
                                    core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
                                      ((alloc.vec.Vec Std.U8) ×
                                      prover.MaskedFixtureAudit)
                                      (core.convert.FromSame verifier.Error)
                                      residual
                                  ok (r16, nonce_store1)
                              | core.ops.control_flow.ControlFlow.Break
                                residual =>
                                let r14 ←
                                  core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
                                    ((alloc.vec.Vec Std.U8) ×
                                    prover.MaskedFixtureAudit)
                                    (core.convert.FromSame verifier.Error)
                                    residual
                                ok (r14, nonce_store1)
                            | core.ops.control_flow.ControlFlow.Break residual
                              =>
                              let r12 ←
                                core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
                                  ((alloc.vec.Vec Std.U8) ×
                                  prover.MaskedFixtureAudit)
                                  (core.convert.FromSame verifier.Error)
                                  residual
                              ok (r12, nonce_store1)
                          | core.ops.control_flow.ControlFlow.Break residual =>
                            let r11 ←
                              core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
                                ((alloc.vec.Vec Std.U8) ×
                                prover.MaskedFixtureAudit)
                                (core.convert.FromSame verifier.Error) residual
                            ok (r11, nonce_store1)
                        else
                          ok (core.result.Result.Err verifier.Error.Semantic,
                            nonce_store1)
                      else
                        ok (core.result.Result.Err verifier.Error.Semantic,
                          nonce_store1)
                    else
                      ok (core.result.Result.Err verifier.Error.Semantic,
                        nonce_store1)
          | core.ops.control_flow.ControlFlow.Break residual =>
            let r10 ←
              core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
                ((alloc.vec.Vec Std.U8) × prover.MaskedFixtureAudit)
                (core.convert.FromSame verifier.Error) residual
            ok (r10, nonce_store1)
        | core.ops.control_flow.ControlFlow.Break residual =>
          let r8 ←
            core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
              ((alloc.vec.Vec Std.U8) × prover.MaskedFixtureAudit)
              (core.convert.FromSame verifier.Error) residual
          ok (r8, nonce_store1)
      | core.ops.control_flow.ControlFlow.Break residual =>
        let r6 ←
          core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
            ((alloc.vec.Vec Std.U8) × prover.MaskedFixtureAudit)
            (core.convert.FromSame verifier.Error) residual
        ok (r6, nonce_store1)
    | core.ops.control_flow.ControlFlow.Break residual =>
      let r4 ←
        core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
          ((alloc.vec.Vec Std.U8) × prover.MaskedFixtureAudit)
          (core.convert.FromSame verifier.Error) residual
      ok (r4, nonce_store1)
  | core.ops.control_flow.ControlFlow.Break residual =>
    let r2 ←
      core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
        ((alloc.vec.Vec Std.U8) × prover.MaskedFixtureAudit)
        (core.convert.FromSame verifier.Error) residual
    ok (r2, nonce_store1)


end R1Z.PV_RE_ComposedSuffix5_073
pv_composed5_source_contexts ProverRwFull.prover.prove_masked_with_attempt
pv_composed5_source_contexts R1Z.PV_RE_ComposedSuffix5_073.continueAfter
