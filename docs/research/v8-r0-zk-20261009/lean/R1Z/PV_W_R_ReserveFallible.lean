import R1Z.PV_W_StructuredBinds
import R1Z.PV_W_RecursiveLaws
import R1Z.PV_W_R_ReservationPath
import R1Z.PV_W_R_SyncDirectory
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_W_R_ReserveFallible
open Aeneas Aeneas.Std ProverRwFull PV_W_ReachedEffects PV_W_Callbacks
variable [ExternalTypes]

def program
  (self : aspis_prover.state_only_entropy.DurableStateOnlyMaskNonceStore)
  (statement_digest : Array Std.U8 32#usize)
  (mask_nonce : Array Std.U8 32#usize) :
  P ((core.result.Result Bool std.io.error.Error) ×
    aspis_prover.state_only_entropy.DurableStateOnlyMaskNonceStore) := do
  let path ← PV_W_R_ReservationPath.program
    { self with last_error := none } mask_nonce
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
  let r ← perform (.base (.optionsOpen (fun dictionary => letI : ExternalFuns := dictionary; std.path.PathBuf.Insts.CoreConvertAsRefPath) options2 path))
  match r with
  | core.result.Result.Ok file =>
    let s ← invoke "Aeneas.Std.lift" (fun ops =>
        letI : ExternalFuns := ops
        Aeneas.Std.lift (Array.to_slice aspis_prover.state_only_entropy.RESERVATION_MAGIC))
    let (r1, file1) ← perform (.base (.writeAll file s))
    let cf ← invoke "core.result.Result.Insts.CoreOpsTry.branch" (fun ops =>
        letI : ExternalFuns := ops
        core.result.Result.Insts.CoreOpsTry.branch r1)
    match cf with
    | core.ops.control_flow.ControlFlow.Continue _ =>
      let s1 ← invoke "Aeneas.Std.lift" (fun ops =>
          letI : ExternalFuns := ops
          Aeneas.Std.lift (Array.to_slice statement_digest))
      let (r2, file2) ← perform (.base (.writeAll file1 s1))
      let cf1 ← invoke "core.result.Result.Insts.CoreOpsTry.branch" (fun ops =>
          letI : ExternalFuns := ops
          core.result.Result.Insts.CoreOpsTry.branch r2)
      match cf1 with
      | core.ops.control_flow.ControlFlow.Continue _ =>
        let s2 ← invoke "Aeneas.Std.lift" (fun ops =>
            letI : ExternalFuns := ops
            Aeneas.Std.lift (Array.to_slice mask_nonce))
        let (r3, file3) ← perform (.base (.writeAll file2 s2))
        let cf2 ← invoke "core.result.Result.Insts.CoreOpsTry.branch" (fun ops =>
            letI : ExternalFuns := ops
            core.result.Result.Insts.CoreOpsTry.branch r3)
        match cf2 with
        | core.ops.control_flow.ControlFlow.Continue _ =>
          let r4 ← perform (.base (.fileSync file3))
          let cf3 ← invoke "core.result.Result.Insts.CoreOpsTry.branch" (fun ops =>
              letI : ExternalFuns := ops
              core.result.Result.Insts.CoreOpsTry.branch r4)
          match cf3 with
          | core.ops.control_flow.ControlFlow.Continue _ =>
            let p ← invoke "std.path.PathBuf.Insts.CoreOpsDerefDerefPath.deref" (fun ops =>
                letI : ExternalFuns := ops
                std.path.PathBuf.Insts.CoreOpsDerefDerefPath.deref self.directory)
            let r5 ← PV_W_R_SyncDirectory.program p
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
    let ek ← perform (.base (.errorKind error))
    let b ← invoke "core.io.error.ErrorKind.Insts.CoreCmpPartialEqErrorKind.eq" (fun ops =>
        letI : ExternalFuns := ops
        core.io.error.ErrorKind.Insts.CoreCmpPartialEqErrorKind.eq ek
        core.io.error.ErrorKind.AlreadyExists)
    PV_W_StructuredBinds.join (do
      if b then
        pure (core.result.Result.Ok false)
      else
        pure (core.result.Result.Err error)) (fun r1 => do
      pure (r1, { self with last_error := none }))

theorem erase_program (ops : ExternalFuns)
  (self : aspis_prover.state_only_entropy.DurableStateOnlyMaskNonceStore)
  (statement_digest : Array Std.U8 32#usize)
  (mask_nonce : Array Std.U8 32#usize) :
  erase ops (program self statement_digest mask_nonce) =
    @aspis_prover.state_only_entropy.DurableStateOnlyMaskNonceStore.reserve_fallible _ ops self statement_digest mask_nonce := by
  unfold program aspis_prover.state_only_entropy.DurableStateOnlyMaskNonceStore.reserve_fallible
  try dsimp only
  rw [erase_bind]
  apply PV_W_RecursiveLaws.bind_congr
  ·
    rw [PV_W_R_ReservationPath.erase_program]
  · intro path
    try dsimp only
    rw [erase_bind]
    apply PV_W_RecursiveLaws.bind_congr
    ·
      exact erase_invoke ops _ _
    · intro options
      try dsimp only
      rw [erase_bind]
      apply PV_W_RecursiveLaws.bind_congr
      ·
        exact erase_invoke ops _ _
      · rintro ⟨oo, write_back⟩
        try dsimp only
        rw [erase_bind]
        apply PV_W_RecursiveLaws.bind_congr
        ·
          exact erase_invoke ops _ _
        · rintro ⟨oo1, create_new_back⟩
          try dsimp only
          try dsimp only
          try dsimp only
          rw [erase_bind]
          apply PV_W_RecursiveLaws.bind_congr
          ·
            exact erase_invoke ops _ _
          · rintro ⟨oo3, mode_back⟩
            try dsimp only
            try dsimp only
            rw [erase_bind]
            apply PV_W_RecursiveLaws.bind_congr
            ·
              exact erase_perform ops _
            · intro r
              try dsimp only
              cases r with
              | Ok file =>
                try dsimp only
                rw [erase_bind]
                apply PV_W_RecursiveLaws.bind_congr
                ·
                  exact erase_invoke ops _ _
                · intro s
                  try dsimp only
                  rw [erase_bind]
                  apply PV_W_RecursiveLaws.bind_congr
                  ·
                    exact erase_perform ops _
                  · rintro ⟨r1, file1⟩
                    try dsimp only
                    rw [erase_bind]
                    apply PV_W_RecursiveLaws.bind_congr
                    ·
                      exact erase_invoke ops _ _
                    · intro cf
                      try dsimp only
                      cases cf with
                      | Continue unused0_0 =>
                        try dsimp only
                        rw [erase_bind]
                        apply PV_W_RecursiveLaws.bind_congr
                        ·
                          exact erase_invoke ops _ _
                        · intro s1
                          try dsimp only
                          rw [erase_bind]
                          apply PV_W_RecursiveLaws.bind_congr
                          ·
                            exact erase_perform ops _
                          · rintro ⟨r2, file2⟩
                            try dsimp only
                            rw [erase_bind]
                            apply PV_W_RecursiveLaws.bind_congr
                            ·
                              exact erase_invoke ops _ _
                            · intro cf1
                              try dsimp only
                              cases cf1 with
                              | Continue unused0_0 =>
                                try dsimp only
                                rw [erase_bind]
                                apply PV_W_RecursiveLaws.bind_congr
                                ·
                                  exact erase_invoke ops _ _
                                · intro s2
                                  try dsimp only
                                  rw [erase_bind]
                                  apply PV_W_RecursiveLaws.bind_congr
                                  ·
                                    exact erase_perform ops _
                                  · rintro ⟨r3, file3⟩
                                    try dsimp only
                                    rw [erase_bind]
                                    apply PV_W_RecursiveLaws.bind_congr
                                    ·
                                      exact erase_invoke ops _ _
                                    · intro cf2
                                      try dsimp only
                                      cases cf2 with
                                      | Continue unused0_0 =>
                                        try dsimp only
                                        rw [erase_bind]
                                        apply PV_W_RecursiveLaws.bind_congr
                                        ·
                                          exact erase_perform ops _
                                        · intro r4
                                          try dsimp only
                                          rw [erase_bind]
                                          apply PV_W_RecursiveLaws.bind_congr
                                          ·
                                            exact erase_invoke ops _ _
                                          · intro cf3
                                            try dsimp only
                                            cases cf3 with
                                            | Continue unused0_0 =>
                                              try dsimp only
                                              rw [erase_bind]
                                              apply PV_W_RecursiveLaws.bind_congr
                                              ·
                                                exact erase_invoke ops _ _
                                              · intro p
                                                try dsimp only
                                                rw [erase_bind]
                                                apply PV_W_RecursiveLaws.bind_congr
                                                ·
                                                  rw [PV_W_R_SyncDirectory.erase_program]
                                                · intro r5
                                                  try dsimp only
                                                  rw [erase_bind]
                                                  apply PV_W_RecursiveLaws.bind_congr
                                                  ·
                                                    exact erase_invoke ops _ _
                                                  · intro cf4
                                                    try dsimp only
                                                    cases cf4 with
                                                    | Continue unused0_0 =>
                                                      rfl
                                                    | Break residual =>
                                                      try dsimp only
                                                      rw [erase_bind]
                                                      apply PV_W_RecursiveLaws.bind_congr
                                                      ·
                                                        exact erase_invoke ops _ _
                                                      · intro r6
                                                        rfl
                                            | Break residual =>
                                              try dsimp only
                                              rw [erase_bind]
                                              apply PV_W_RecursiveLaws.bind_congr
                                              ·
                                                exact erase_invoke ops _ _
                                              · intro r5
                                                rfl
                                      | Break residual =>
                                        try dsimp only
                                        rw [erase_bind]
                                        apply PV_W_RecursiveLaws.bind_congr
                                        ·
                                          exact erase_invoke ops _ _
                                        · intro r4
                                          rfl
                              | Break residual =>
                                try dsimp only
                                rw [erase_bind]
                                apply PV_W_RecursiveLaws.bind_congr
                                ·
                                  exact erase_invoke ops _ _
                                · intro r3
                                  rfl
                      | Break residual =>
                        try dsimp only
                        rw [erase_bind]
                        apply PV_W_RecursiveLaws.bind_congr
                        ·
                          exact erase_invoke ops _ _
                        · intro r2
                          rfl
              | Err error =>
                try dsimp only
                rw [erase_bind]
                apply PV_W_RecursiveLaws.bind_congr
                ·
                  exact erase_perform ops _
                · intro ek
                  try dsimp only
                  rw [erase_bind]
                  apply PV_W_RecursiveLaws.bind_congr
                  ·
                    exact erase_invoke ops _ _
                  · intro b
                    rw [PV_W_StructuredBinds.erase_join]
                    apply PV_W_RecursiveLaws.bind_congr
                    ·
                      try dsimp only
                      apply PV_W_Callbacks.erase_if_congr
                      ·
                        rfl
                      ·
                        rfl
                    · intro r1
                      rfl

#print axioms erase_program
end R1Z.PV_W_R_ReserveFallible
