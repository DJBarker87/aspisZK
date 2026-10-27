import R1Z.ProverRwFullFuns
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RE_Continue041
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

/-- No branch is discarded; the continuation is named rather than existential. -/
theorem equation (self : aspis_prover.state_only_entropy.DurableStateOnlyMaskNonceStore) (statement_digest : Array Std.U8 32#usize) (mask_nonce : Array Std.U8 32#usize) :
    aspis_prover.state_only_entropy.DurableStateOnlyMaskNonceStore.reserve_fallible (self := self) (statement_digest := statement_digest) (mask_nonce := mask_nonce) =
      (aspis_prover.state_only_entropy.DurableStateOnlyMaskNonceStore.reservation_path
      { self with last_error := none } mask_nonce >>= fun out => continueAfter (self := self) (statement_digest := statement_digest) (mask_nonce := mask_nonce) out) := by
  rw [aspis_prover.state_only_entropy.DurableStateOnlyMaskNonceStore.reserve_fallible]
  rfl

/-- Exact successful transition to the source suffix. The guard is not
asserted for native fixtures. -/
theorem success (self : aspis_prover.state_only_entropy.DurableStateOnlyMaskNonceStore) (statement_digest : Array Std.U8 32#usize) (mask_nonce : Array Std.U8 32#usize) (out : Payload (aspis_prover.state_only_entropy.DurableStateOnlyMaskNonceStore.reservation_path
      { self with last_error := none } mask_nonce))
    (h : (aspis_prover.state_only_entropy.DurableStateOnlyMaskNonceStore.reservation_path
      { self with last_error := none } mask_nonce) = .ok out) :
    aspis_prover.state_only_entropy.DurableStateOnlyMaskNonceStore.reserve_fallible (self := self) (statement_digest := statement_digest) (mask_nonce := mask_nonce) = continueAfter (self := self) (statement_digest := statement_digest) (mask_nonce := mask_nonce) out := by
  rw [equation, h]
  rfl

/-- Exact failure truncation, without reducing the suffix. -/
theorem failure (self : aspis_prover.state_only_entropy.DurableStateOnlyMaskNonceStore) (statement_digest : Array Std.U8 32#usize) (mask_nonce : Array Std.U8 32#usize) (e : Error)
    (h : (aspis_prover.state_only_entropy.DurableStateOnlyMaskNonceStore.reservation_path
      { self with last_error := none } mask_nonce) = .fail e) :
    aspis_prover.state_only_entropy.DurableStateOnlyMaskNonceStore.reserve_fallible (self := self) (statement_digest := statement_digest) (mask_nonce := mask_nonce) = .fail e := by
  rw [equation, h]
  rfl

/-- Divergence does not enter the suffix. -/
theorem diverges (self : aspis_prover.state_only_entropy.DurableStateOnlyMaskNonceStore) (statement_digest : Array Std.U8 32#usize) (mask_nonce : Array Std.U8 32#usize)
    (h : (aspis_prover.state_only_entropy.DurableStateOnlyMaskNonceStore.reservation_path
      { self with last_error := none } mask_nonce) = .div) :
    aspis_prover.state_only_entropy.DurableStateOnlyMaskNonceStore.reserve_fallible (self := self) (statement_digest := statement_digest) (mask_nonce := mask_nonce) = .div := by
  rw [equation, h]
  rfl

#print axioms continueAfter
#print axioms equation
#print axioms success
#print axioms failure
#print axioms diverges
end R1Z.PV_RE_Continue041
