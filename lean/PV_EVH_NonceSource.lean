import PV_EVH_NonceWorld
set_option autoImplicit false
noncomputable section
namespace PV_EVH_NonceSource
open Aeneas Aeneas.Std ProverRwFull
open PV_EVH_World PV_EVH_NonceWorld
variable [ExternalTypes] [ExternalFuns]
/- Selected file-call spines only. reservation_path and the other lifted
helpers remain Result-only: allocation/hash/drop source adequacy is OPEN. -/

def syncDirectory (a : Answers)
  (directory : std.path.Path) : M (core.result.Result Unit std.io.error.Error) := do
  let r ← openFile a (Shared0T.Insts.CoreConvertAsRef
      std.path.Path.Insts.CoreConvertAsRefPath) directory
  let cf ← PV_EVH_World.lift (core.result.Result.Insts.CoreOpsTry.branch r)
  match cf with
  | core.ops.control_flow.ControlFlow.Continue val =>
    sync a val
  | core.ops.control_flow.ControlFlow.Break residual =>
    PV_EVH_World.lift (core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
      Unit (core.convert.FromSame std.io.error.Error) residual)

theorem syncDirectory_fixed (a : Answers) (h : Compatible a)
  (directory : std.path.Path) :
    FixedView (syncDirectory a directory) (aspis_prover.state_only_entropy.sync_directory directory) := by
  unfold syncDirectory aspis_prover.state_only_entropy.sync_directory
  try dsimp only
  apply fixed_bind
  ·
    exact open_fixed a _ _ (fun w => h.openFile _ _ w)
  · intro r
    try dsimp only
    apply fixed_bind
    ·
      exact fixed_lift _
    · intro cf
      try dsimp only
      cases cf with
      | Continue val =>
        exact sync_fixed a _ (fun w => h.sync w _)
      | Break residual =>
        exact fixed_lift _

#print axioms syncDirectory_fixed

def reserveFallible (a : Answers)
  (self : aspis_prover.state_only_entropy.DurableStateOnlyMaskNonceStore)
  (statement_digest : Array Std.U8 32#usize)
  (mask_nonce : Array Std.U8 32#usize) : M ((core.result.Result Bool std.io.error.Error) ×
    aspis_prover.state_only_entropy.DurableStateOnlyMaskNonceStore) := do
  let path ← PV_EVH_World.lift (aspis_prover.state_only_entropy.DurableStateOnlyMaskNonceStore.reservation_path
      { self with last_error := none } mask_nonce)
  let options ← PV_EVH_World.lift (std.fs.OpenOptions.new)
  let (oo, write_back) ← PV_EVH_World.lift (std.fs.OpenOptions.write options true)
  let (oo1, create_new_back) ← PV_EVH_World.lift (std.fs.OpenOptions.create_new oo true)
  let oo2 := create_new_back oo1
  let options1 := write_back oo2
  let (oo3, mode_back) ← PV_EVH_World.lift (std.fs.OpenOptions.Insts.StdOsUnixFsOpenOptionsExt.mode options1 384#u32)
  let options2 := mode_back oo3
  let r ← optionsOpen a std.path.PathBuf.Insts.CoreConvertAsRefPath
      options2 path
  match r with
  | core.result.Result.Ok file =>
    let s ← PV_EVH_World.lift (Aeneas.Std.lift (Array.to_slice aspis_prover.state_only_entropy.RESERVATION_MAGIC))
    let (r1, file1) ← writeAll a file s
    let cf ← PV_EVH_World.lift (core.result.Result.Insts.CoreOpsTry.branch r1)
    match cf with
    | core.ops.control_flow.ControlFlow.Continue _ =>
      let s1 ← PV_EVH_World.lift (Aeneas.Std.lift (Array.to_slice statement_digest))
      let (r2, file2) ← writeAll a file1 s1
      let cf1 ← PV_EVH_World.lift (core.result.Result.Insts.CoreOpsTry.branch r2)
      match cf1 with
      | core.ops.control_flow.ControlFlow.Continue _ =>
        let s2 ← PV_EVH_World.lift (Aeneas.Std.lift (Array.to_slice mask_nonce))
        let (r3, file3) ← writeAll a file2 s2
        let cf2 ← PV_EVH_World.lift (core.result.Result.Insts.CoreOpsTry.branch r3)
        match cf2 with
        | core.ops.control_flow.ControlFlow.Continue _ =>
          let r4 ← sync a file3
          let cf3 ← PV_EVH_World.lift (core.result.Result.Insts.CoreOpsTry.branch r4)
          match cf3 with
          | core.ops.control_flow.ControlFlow.Continue _ =>
            let p ← PV_EVH_World.lift (std.path.PathBuf.Insts.CoreOpsDerefDerefPath.deref self.directory)
            let r5 ← syncDirectory a p
            let cf4 ← PV_EVH_World.lift (core.result.Result.Insts.CoreOpsTry.branch r5)
            match cf4 with
            | core.ops.control_flow.ControlFlow.Continue _ =>
              pure (core.result.Result.Ok true, { self with last_error := none })
            | core.ops.control_flow.ControlFlow.Break residual =>
              let r6 ← PV_EVH_World.lift (core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
                  Bool (core.convert.FromSame std.io.error.Error) residual)
              pure (r6, { self with last_error := none })
          | core.ops.control_flow.ControlFlow.Break residual =>
            let r5 ← PV_EVH_World.lift (core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
                Bool (core.convert.FromSame std.io.error.Error) residual)
            pure (r5, { self with last_error := none })
        | core.ops.control_flow.ControlFlow.Break residual =>
          let r4 ← PV_EVH_World.lift (core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
              Bool (core.convert.FromSame std.io.error.Error) residual)
          pure (r4, { self with last_error := none })
      | core.ops.control_flow.ControlFlow.Break residual =>
        let r3 ← PV_EVH_World.lift (core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
            Bool (core.convert.FromSame std.io.error.Error) residual)
        pure (r3, { self with last_error := none })
    | core.ops.control_flow.ControlFlow.Break residual =>
      let r2 ← PV_EVH_World.lift (core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
          Bool (core.convert.FromSame std.io.error.Error) residual)
      pure (r2, { self with last_error := none })
  | core.result.Result.Err error =>
    let ek ← PV_EVH_World.lift (std.io.error.Error.kind error)
    let b ← PV_EVH_World.lift (core.io.error.ErrorKind.Insts.CoreCmpPartialEqErrorKind.eq ek
        core.io.error.ErrorKind.AlreadyExists)
    let r1 ← do
      if b then
        pure (core.result.Result.Ok false)
      else
        pure (core.result.Result.Err error)
    pure (r1, { self with last_error := none })

theorem reserveFallible_fixed (a : Answers) (h : Compatible a)
  (self : aspis_prover.state_only_entropy.DurableStateOnlyMaskNonceStore)
  (statement_digest : Array Std.U8 32#usize)
  (mask_nonce : Array Std.U8 32#usize) :
    FixedView (reserveFallible a self statement_digest mask_nonce) (aspis_prover.state_only_entropy.DurableStateOnlyMaskNonceStore.reserve_fallible self statement_digest mask_nonce) := by
  unfold reserveFallible aspis_prover.state_only_entropy.DurableStateOnlyMaskNonceStore.reserve_fallible
  try dsimp only
  apply fixed_bind
  ·
    exact fixed_lift _
  · intro path
    try dsimp only
    apply fixed_bind
    ·
      exact fixed_lift _
    · intro options
      try dsimp only
      apply fixed_bind
      ·
        exact fixed_lift _
      · rintro ⟨oo, write_back⟩
        try dsimp only
        apply fixed_bind
        ·
          exact fixed_lift _
        · rintro ⟨oo1, create_new_back⟩
          let oo2 := create_new_back oo1
          try dsimp only
          let options1 := write_back oo2
          try dsimp only
          try dsimp only
          apply fixed_bind
          ·
            exact fixed_lift _
          · rintro ⟨oo3, mode_back⟩
            let options2 := mode_back oo3
            try dsimp only
            try dsimp only
            apply fixed_bind
            ·
              exact options_fixed a _ _ _ (fun w => h.options _ _ _ w)
            · intro r
              try dsimp only
              cases r with
              | Ok file =>
                try dsimp only
                apply fixed_bind (r := (do
                  Aeneas.Std.lift (Array.to_slice aspis_prover.state_only_entropy.RESERVATION_MAGIC))) (f := fun s => (show Result ((core.result.Result Bool std.io.error.Error) ×
    aspis_prover.state_only_entropy.DurableStateOnlyMaskNonceStore) from do
                  let (r1, file1) ← std.fs.File.Insts.StdIoWrite.write_all file s
                  let cf ← core.result.Result.Insts.CoreOpsTry.branch r1
                  match cf with
                  | core.ops.control_flow.ControlFlow.Continue _ =>
                    let s1 ← Aeneas.Std.lift (Array.to_slice statement_digest)
                    let (r2, file2) ← std.fs.File.Insts.StdIoWrite.write_all file1 s1
                    let cf1 ← core.result.Result.Insts.CoreOpsTry.branch r2
                    match cf1 with
                    | core.ops.control_flow.ControlFlow.Continue _ =>
                      let s2 ← Aeneas.Std.lift (Array.to_slice mask_nonce)
                      let (r3, file3) ← std.fs.File.Insts.StdIoWrite.write_all file2 s2
                      let cf2 ← core.result.Result.Insts.CoreOpsTry.branch r3
                      match cf2 with
                      | core.ops.control_flow.ControlFlow.Continue _ =>
                        let r4 ← std.fs.File.sync_all file3
                        let cf3 ← core.result.Result.Insts.CoreOpsTry.branch r4
                        match cf3 with
                        | core.ops.control_flow.ControlFlow.Continue _ =>
                          let p ← std.path.PathBuf.Insts.CoreOpsDerefDerefPath.deref self.directory
                          let r5 ← aspis_prover.state_only_entropy.sync_directory p
                          let cf4 ← core.result.Result.Insts.CoreOpsTry.branch r5
                          match cf4 with
                          | core.ops.control_flow.ControlFlow.Continue _ =>
                            Result.ok (core.result.Result.Ok true, { self with last_error := none })
                          | core.ops.control_flow.ControlFlow.Break residual =>
                            let r6 ← core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
                                Bool (core.convert.FromSame std.io.error.Error) residual
                            Result.ok (r6, { self with last_error := none })
                        | core.ops.control_flow.ControlFlow.Break residual =>
                          let r5 ← core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
                              Bool (core.convert.FromSame std.io.error.Error) residual
                          Result.ok (r5, { self with last_error := none })
                      | core.ops.control_flow.ControlFlow.Break residual =>
                        let r4 ← core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
                            Bool (core.convert.FromSame std.io.error.Error) residual
                        Result.ok (r4, { self with last_error := none })
                    | core.ops.control_flow.ControlFlow.Break residual =>
                      let r3 ← core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
                          Bool (core.convert.FromSame std.io.error.Error) residual
                      Result.ok (r3, { self with last_error := none })
                  | core.ops.control_flow.ControlFlow.Break residual =>
                    let r2 ← core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
                        Bool (core.convert.FromSame std.io.error.Error) residual
                    Result.ok (r2, { self with last_error := none })))
                ·
                  exact fixed_lift _
                · intro s
                  try dsimp only
                  apply fixed_bind
                  ·
                    exact write_fixed a _ _ (fun w => h.write w _ _)
                  · rintro ⟨r1, file1⟩
                    try dsimp only
                    apply fixed_bind
                    ·
                      exact fixed_lift _
                    · intro cf
                      try dsimp only
                      cases cf with
                      | Continue unused0 =>
                        try dsimp only
                        apply fixed_bind (r := (do
                          Aeneas.Std.lift (Array.to_slice statement_digest))) (f := fun s1 => (show Result ((core.result.Result Bool std.io.error.Error) ×
    aspis_prover.state_only_entropy.DurableStateOnlyMaskNonceStore) from do
                          let (r2, file2) ← std.fs.File.Insts.StdIoWrite.write_all file1 s1
                          let cf1 ← core.result.Result.Insts.CoreOpsTry.branch r2
                          match cf1 with
                          | core.ops.control_flow.ControlFlow.Continue _ =>
                            let s2 ← Aeneas.Std.lift (Array.to_slice mask_nonce)
                            let (r3, file3) ← std.fs.File.Insts.StdIoWrite.write_all file2 s2
                            let cf2 ← core.result.Result.Insts.CoreOpsTry.branch r3
                            match cf2 with
                            | core.ops.control_flow.ControlFlow.Continue _ =>
                              let r4 ← std.fs.File.sync_all file3
                              let cf3 ← core.result.Result.Insts.CoreOpsTry.branch r4
                              match cf3 with
                              | core.ops.control_flow.ControlFlow.Continue _ =>
                                let p ← std.path.PathBuf.Insts.CoreOpsDerefDerefPath.deref self.directory
                                let r5 ← aspis_prover.state_only_entropy.sync_directory p
                                let cf4 ← core.result.Result.Insts.CoreOpsTry.branch r5
                                match cf4 with
                                | core.ops.control_flow.ControlFlow.Continue _ =>
                                  Result.ok (core.result.Result.Ok true, { self with last_error := none })
                                | core.ops.control_flow.ControlFlow.Break residual =>
                                  let r6 ← core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
                                      Bool (core.convert.FromSame std.io.error.Error) residual
                                  Result.ok (r6, { self with last_error := none })
                              | core.ops.control_flow.ControlFlow.Break residual =>
                                let r5 ← core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
                                    Bool (core.convert.FromSame std.io.error.Error) residual
                                Result.ok (r5, { self with last_error := none })
                            | core.ops.control_flow.ControlFlow.Break residual =>
                              let r4 ← core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
                                  Bool (core.convert.FromSame std.io.error.Error) residual
                              Result.ok (r4, { self with last_error := none })
                          | core.ops.control_flow.ControlFlow.Break residual =>
                            let r3 ← core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
                                Bool (core.convert.FromSame std.io.error.Error) residual
                            Result.ok (r3, { self with last_error := none })))
                        ·
                          exact fixed_lift _
                        · intro s1
                          try dsimp only
                          apply fixed_bind
                          ·
                            exact write_fixed a _ _ (fun w => h.write w _ _)
                          · rintro ⟨r2, file2⟩
                            try dsimp only
                            apply fixed_bind
                            ·
                              exact fixed_lift _
                            · intro cf1
                              try dsimp only
                              cases cf1 with
                              | Continue unused0 =>
                                try dsimp only
                                apply fixed_bind (r := (do
                                  Aeneas.Std.lift (Array.to_slice mask_nonce))) (f := fun s2 => (show Result ((core.result.Result Bool std.io.error.Error) ×
    aspis_prover.state_only_entropy.DurableStateOnlyMaskNonceStore) from do
                                  let (r3, file3) ← std.fs.File.Insts.StdIoWrite.write_all file2 s2
                                  let cf2 ← core.result.Result.Insts.CoreOpsTry.branch r3
                                  match cf2 with
                                  | core.ops.control_flow.ControlFlow.Continue _ =>
                                    let r4 ← std.fs.File.sync_all file3
                                    let cf3 ← core.result.Result.Insts.CoreOpsTry.branch r4
                                    match cf3 with
                                    | core.ops.control_flow.ControlFlow.Continue _ =>
                                      let p ← std.path.PathBuf.Insts.CoreOpsDerefDerefPath.deref self.directory
                                      let r5 ← aspis_prover.state_only_entropy.sync_directory p
                                      let cf4 ← core.result.Result.Insts.CoreOpsTry.branch r5
                                      match cf4 with
                                      | core.ops.control_flow.ControlFlow.Continue _ =>
                                        Result.ok (core.result.Result.Ok true, { self with last_error := none })
                                      | core.ops.control_flow.ControlFlow.Break residual =>
                                        let r6 ← core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
                                            Bool (core.convert.FromSame std.io.error.Error) residual
                                        Result.ok (r6, { self with last_error := none })
                                    | core.ops.control_flow.ControlFlow.Break residual =>
                                      let r5 ← core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
                                          Bool (core.convert.FromSame std.io.error.Error) residual
                                      Result.ok (r5, { self with last_error := none })
                                  | core.ops.control_flow.ControlFlow.Break residual =>
                                    let r4 ← core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
                                        Bool (core.convert.FromSame std.io.error.Error) residual
                                    Result.ok (r4, { self with last_error := none })))
                                ·
                                  exact fixed_lift _
                                · intro s2
                                  try dsimp only
                                  apply fixed_bind
                                  ·
                                    exact write_fixed a _ _ (fun w => h.write w _ _)
                                  · rintro ⟨r3, file3⟩
                                    try dsimp only
                                    apply fixed_bind
                                    ·
                                      exact fixed_lift _
                                    · intro cf2
                                      try dsimp only
                                      cases cf2 with
                                      | Continue unused0 =>
                                        try dsimp only
                                        apply fixed_bind
                                        ·
                                          exact sync_fixed a _ (fun w => h.sync w _)
                                        · intro r4
                                          try dsimp only
                                          apply fixed_bind
                                          ·
                                            exact fixed_lift _
                                          · intro cf3
                                            try dsimp only
                                            cases cf3 with
                                            | Continue unused0 =>
                                              try dsimp only
                                              apply fixed_bind
                                              ·
                                                exact fixed_lift _
                                              · intro p
                                                try dsimp only
                                                apply fixed_bind
                                                ·
                                                  apply syncDirectory_fixed a h
                                                · intro r5
                                                  try dsimp only
                                                  apply fixed_bind
                                                  ·
                                                    exact fixed_lift _
                                                  · intro cf4
                                                    try dsimp only
                                                    cases cf4 with
                                                    | Continue unused0 =>
                                                      exact fixed_lift _
                                                    | Break residual =>
                                                      try dsimp only
                                                      apply fixed_bind
                                                      ·
                                                        exact fixed_lift _
                                                      · intro r6
                                                        exact fixed_lift _
                                            | Break residual =>
                                              try dsimp only
                                              apply fixed_bind
                                              ·
                                                exact fixed_lift _
                                              · intro r5
                                                exact fixed_lift _
                                      | Break residual =>
                                        try dsimp only
                                        apply fixed_bind
                                        ·
                                          exact fixed_lift _
                                        · intro r4
                                          exact fixed_lift _
                              | Break residual =>
                                try dsimp only
                                apply fixed_bind
                                ·
                                  exact fixed_lift _
                                · intro r3
                                  exact fixed_lift _
                      | Break residual =>
                        try dsimp only
                        apply fixed_bind
                        ·
                          exact fixed_lift _
                        · intro r2
                          exact fixed_lift _
              | Err error =>
                try dsimp only
                apply fixed_bind
                ·
                  exact fixed_lift _
                · intro ek
                  try dsimp only
                  apply fixed_bind
                  ·
                    exact fixed_lift _
                  · intro b
                    by_cases condition : b
                    · simp only [condition,if_true]
                      intro w; rfl
                    · simp only [condition,if_false]
                      intro w; rfl

#print axioms reserveFallible_fixed

def reserve (a : Answers)
  (self : aspis_prover.state_only_entropy.DurableStateOnlyMaskNonceStore)
  (statement_digest : Array Std.U8 32#usize)
  (mask_nonce : Array Std.U8 32#usize) : M (Bool ×
    aspis_prover.state_only_entropy.DurableStateOnlyMaskNonceStore) := do
  let (r, self1) ← reserveFallible a
      self statement_digest mask_nonce
  match r with
  | core.result.Result.Ok reserved =>
    pure (reserved, self1)
  | core.result.Result.Err error =>
    let ek ← PV_EVH_World.lift (std.io.error.Error.kind error)
    pure (false, { self1 with last_error := (some ek) })

theorem reserve_fixed (a : Answers) (h : Compatible a)
  (self : aspis_prover.state_only_entropy.DurableStateOnlyMaskNonceStore)
  (statement_digest : Array Std.U8 32#usize)
  (mask_nonce : Array Std.U8 32#usize) :
    FixedView (reserve a self statement_digest mask_nonce) (aspis_prover.state_only_entropy.DurableStateOnlyMaskNonceStore.Insts.Aspis_proverState_only_hidingStateOnlyMaskNonceStore.reserve self statement_digest mask_nonce) := by
  unfold reserve aspis_prover.state_only_entropy.DurableStateOnlyMaskNonceStore.Insts.Aspis_proverState_only_hidingStateOnlyMaskNonceStore.reserve
  try dsimp only
  apply fixed_bind
  ·
    apply reserveFallible_fixed a h
  · rintro ⟨r, self1⟩
    try dsimp only
    cases r with
    | Ok reserved =>
      exact fixed_lift _
    | Err error =>
      try dsimp only
      apply fixed_bind
      ·
        exact fixed_lift _
      · intro ek
        exact fixed_lift _

#print axioms reserve_fixed
end PV_EVH_NonceSource
