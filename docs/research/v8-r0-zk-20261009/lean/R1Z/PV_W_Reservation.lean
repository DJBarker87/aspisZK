import R1Z.PV_W_SourceSyntax
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_W_Reservation
open ProverRwFull PV_W_SourceSyntax PV_W_Syntax PV_W_Threading
open Aeneas.Std
variable [ExternalTypes]

/-- Generated syntax; helpers retain unexecuted source-call thunks. -/
def syncDirectory
  (directory : std.path.Path) : P (core.result.Result Unit std.io.error.Error) := do
  let r ← invoke "std.fs.File.open" (fun ops =>
    letI : ExternalFuns := ops
    std.fs.File.open (Shared0T.Insts.CoreConvertAsRef
    std.path.Path.Insts.CoreConvertAsRefPath) directory)
  let cf ← invoke "core.result.Result.Insts.CoreOpsTry.branch" (fun ops =>
    letI : ExternalFuns := ops
    core.result.Result.Insts.CoreOpsTry.branch r)
  match cf with
  | core.ops.control_flow.ControlFlow.Continue val =>
    invoke "std.fs.File.sync_all" (fun ops =>
      letI : ExternalFuns := ops
      std.fs.File.sync_all val)
  | core.ops.control_flow.ControlFlow.Break residual =>
    invoke "core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual" (fun ops =>
      letI : ExternalFuns := ops
      core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
      Unit (core.convert.FromSame std.io.error.Error) residual)

/-- Generated syntax; helpers retain unexecuted source-call thunks. -/
def reserveFallible
  (self : aspis_prover.state_only_entropy.DurableStateOnlyMaskNonceStore)
  (statement_digest mask_nonce : Array Aeneas.Std.U8 32#usize) :
  P ((core.result.Result Bool std.io.error.Error) × aspis_prover.state_only_entropy.DurableStateOnlyMaskNonceStore) := do
  let path ← invoke "aspis_prover.state_only_entropy.DurableStateOnlyMaskNonceStore.reservation_path" (fun ops =>
    letI : ExternalFuns := ops
    aspis_prover.state_only_entropy.DurableStateOnlyMaskNonceStore.reservation_path
    { self with last_error := none } mask_nonce)
  let options ← invoke "std.fs.OpenOptions.new" (fun ops =>
    letI : ExternalFuns := ops
    std.fs.OpenOptions.new)
  let (oo, write_back) ← invoke "std.fs.OpenOptions.write" (fun ops =>
    letI : ExternalFuns := ops
    std.fs.OpenOptions.write options true)
  let (oo1, create_new_back) ← invoke "std.fs.OpenOptions.create_new" (fun ops =>
    letI : ExternalFuns := ops
    std.fs.OpenOptions.create_new oo true)
  let oo2 := create_new_back oo1
  let options1 := write_back oo2
  let (oo3, mode_back) ← invoke "std.fs.OpenOptions.Insts.StdOsUnixFsOpenOptionsExt.mode" (fun ops =>
    letI : ExternalFuns := ops
    std.fs.OpenOptions.Insts.StdOsUnixFsOpenOptionsExt.mode options1 384#u32)
  let options2 := mode_back oo3
  let r ← invoke "std.fs.OpenOptions.open" (fun ops =>
    letI : ExternalFuns := ops
    std.fs.OpenOptions.open std.path.PathBuf.Insts.CoreConvertAsRefPath
    options2 path)
  match r with
  | core.result.Result.Ok file =>
    let s ← invoke "Aeneas.Std.lift" (fun ops =>
      letI : ExternalFuns := ops
      Aeneas.Std.lift (Array.to_slice aspis_prover.state_only_entropy.RESERVATION_MAGIC))
    let (r1, file1) ← invoke "std.fs.File.Insts.StdIoWrite.write_all" (fun ops =>
      letI : ExternalFuns := ops
      std.fs.File.Insts.StdIoWrite.write_all file s)
    let cf ← invoke "core.result.Result.Insts.CoreOpsTry.branch" (fun ops =>
      letI : ExternalFuns := ops
      core.result.Result.Insts.CoreOpsTry.branch r1)
    match cf with
    | core.ops.control_flow.ControlFlow.Continue _ =>
      let s1 ← invoke "Aeneas.Std.lift" (fun ops =>
        letI : ExternalFuns := ops
        Aeneas.Std.lift (Array.to_slice statement_digest))
      let (r2, file2) ← invoke "std.fs.File.Insts.StdIoWrite.write_all" (fun ops =>
        letI : ExternalFuns := ops
        std.fs.File.Insts.StdIoWrite.write_all file1 s1)
      let cf1 ← invoke "core.result.Result.Insts.CoreOpsTry.branch" (fun ops =>
        letI : ExternalFuns := ops
        core.result.Result.Insts.CoreOpsTry.branch r2)
      match cf1 with
      | core.ops.control_flow.ControlFlow.Continue _ =>
        let s2 ← invoke "Aeneas.Std.lift" (fun ops =>
          letI : ExternalFuns := ops
          Aeneas.Std.lift (Array.to_slice mask_nonce))
        let (r3, file3) ← invoke "std.fs.File.Insts.StdIoWrite.write_all" (fun ops =>
          letI : ExternalFuns := ops
          std.fs.File.Insts.StdIoWrite.write_all file2 s2)
        let cf2 ← invoke "core.result.Result.Insts.CoreOpsTry.branch" (fun ops =>
          letI : ExternalFuns := ops
          core.result.Result.Insts.CoreOpsTry.branch r3)
        match cf2 with
        | core.ops.control_flow.ControlFlow.Continue _ =>
          let r4 ← invoke "std.fs.File.sync_all" (fun ops =>
            letI : ExternalFuns := ops
            std.fs.File.sync_all file3)
          let cf3 ← invoke "core.result.Result.Insts.CoreOpsTry.branch" (fun ops =>
            letI : ExternalFuns := ops
            core.result.Result.Insts.CoreOpsTry.branch r4)
          match cf3 with
          | core.ops.control_flow.ControlFlow.Continue _ =>
            let p ← invoke "std.path.PathBuf.Insts.CoreOpsDerefDerefPath.deref" (fun ops =>
              letI : ExternalFuns := ops
              std.path.PathBuf.Insts.CoreOpsDerefDerefPath.deref self.directory)
            let r5 ← syncDirectory p
            let cf4 ← invoke "core.result.Result.Insts.CoreOpsTry.branch" (fun ops =>
              letI : ExternalFuns := ops
              core.result.Result.Insts.CoreOpsTry.branch r5)
            match cf4 with
            | core.ops.control_flow.ControlFlow.Continue _ =>
              pure (core.result.Result.Ok true, { self with last_error := none })
            | core.ops.control_flow.ControlFlow.Break residual =>
              let r6 ← invoke "core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual" (fun ops =>
                letI : ExternalFuns := ops
                core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
                Bool (core.convert.FromSame std.io.error.Error) residual)
              pure (r6, { self with last_error := none })
          | core.ops.control_flow.ControlFlow.Break residual =>
            let r5 ← invoke "core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual" (fun ops =>
              letI : ExternalFuns := ops
              core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
              Bool (core.convert.FromSame std.io.error.Error) residual)
            pure (r5, { self with last_error := none })
        | core.ops.control_flow.ControlFlow.Break residual =>
          let r4 ← invoke "core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual" (fun ops =>
            letI : ExternalFuns := ops
            core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
            Bool (core.convert.FromSame std.io.error.Error) residual)
          pure (r4, { self with last_error := none })
      | core.ops.control_flow.ControlFlow.Break residual =>
        let r3 ← invoke "core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual" (fun ops =>
          letI : ExternalFuns := ops
          core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
          Bool (core.convert.FromSame std.io.error.Error) residual)
        pure (r3, { self with last_error := none })
    | core.ops.control_flow.ControlFlow.Break residual =>
      let r2 ← invoke "core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual" (fun ops =>
        letI : ExternalFuns := ops
        core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
        Bool (core.convert.FromSame std.io.error.Error) residual)
      pure (r2, { self with last_error := none })
  | core.result.Result.Err error =>
    let ek ← invoke "std.io.error.Error.kind" (fun ops =>
      letI : ExternalFuns := ops
      std.io.error.Error.kind error)
    let b ← invoke "core.io.error.ErrorKind.Insts.CoreCmpPartialEqErrorKind.eq" (fun ops =>
      letI : ExternalFuns := ops
      core.io.error.ErrorKind.Insts.CoreCmpPartialEqErrorKind.eq ek
      core.io.error.ErrorKind.AlreadyExists)
    let r1 ← invoke "if" (fun ops =>
      letI : ExternalFuns := ops
      if b
      then Aeneas.Std.Result.ok (core.result.Result.Ok false)
      else Aeneas.Std.Result.ok (core.result.Result.Err error))
    pure (r1, { self with last_error := none })

/-- Generated syntax; helpers retain unexecuted source-call thunks. -/
def reserve
  (self : aspis_prover.state_only_entropy.DurableStateOnlyMaskNonceStore)
  (statement_digest mask_nonce : Array Aeneas.Std.U8 32#usize) :
  P (Bool × aspis_prover.state_only_entropy.DurableStateOnlyMaskNonceStore) := do
  let (r, self1) ← reserveFallible
    self statement_digest mask_nonce
  match r with
  | core.result.Result.Ok reserved =>
    pure (reserved, self1)
  | core.result.Result.Err error =>
    let ek ← invoke "std.io.error.Error.kind" (fun ops =>
      letI : ExternalFuns := ops
      std.io.error.Error.kind error)
    pure (false, { self1 with last_error := (some ek) })

theorem erase_syncDirectory (ops : ExternalFuns) (directory : std.path.Path) :
    erase ops (syncDirectory directory) =
      @aspis_prover.state_only_entropy.sync_directory _ ops directory := by
  unfold syncDirectory aspis_prover.state_only_entropy.sync_directory
  repeat' first
  | rfl
  | rw [erase_bind]
  | rw [erase_invoke]
  | rw [erase_pure]
  | pv_source_bind
  | funext x
  | split

theorem erase_reserveFallible (ops : ExternalFuns)
    (self : aspis_prover.state_only_entropy.DurableStateOnlyMaskNonceStore)
    (statement nonce : Array U8 32#usize) :
    erase ops (reserveFallible self statement nonce) =
      @aspis_prover.state_only_entropy.DurableStateOnlyMaskNonceStore.reserve_fallible
        _ ops self statement nonce := by
  unfold reserveFallible aspis_prover.state_only_entropy.DurableStateOnlyMaskNonceStore.reserve_fallible
  repeat' first
  | rfl
  | rw [erase_bind]
  | rw [erase_invoke]
  | rw [erase_pure]
  | rw [erase_syncDirectory]
  | pv_source_bind
  | funext x
  | split

theorem erase_reserve (ops : ExternalFuns)
    (self : aspis_prover.state_only_entropy.DurableStateOnlyMaskNonceStore)
    (statement nonce : Array U8 32#usize) :
    erase ops (reserve self statement nonce) =
      @aspis_prover.state_only_entropy.DurableStateOnlyMaskNonceStore.Insts.Aspis_proverState_only_hidingStateOnlyMaskNonceStore.reserve
        _ ops self statement nonce := by
  unfold reserve aspis_prover.state_only_entropy.DurableStateOnlyMaskNonceStore.Insts.Aspis_proverState_only_hidingStateOnlyMaskNonceStore.reserve
  repeat' first
  | rfl
  | rw [erase_bind]
  | rw [erase_invoke]
  | rw [erase_pure]
  | rw [erase_reserveFallible]
  | pv_source_bind
  | funext x
  | split

#print axioms erase_syncDirectory
#print axioms erase_reserveFallible
#print axioms erase_reserve
end R1Z.PV_W_Reservation
