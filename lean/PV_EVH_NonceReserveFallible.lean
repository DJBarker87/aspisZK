import PV_EVH_NonceWorld
import PV_EVH_NoncePath
import PV_EVH_SyncDirectory
import PV_EVH_Prefix
set_option autoImplicit false
noncomputable section
namespace PV_EVH_NonceReserveFallible
open Aeneas Aeneas.Std ProverRwFull PV_EVH_World
open PV_EVH_Prefix (P FinishedView)
variable [ExternalTypes] [ExternalFuns]

/-- Every non-language callee is explicitly OPEN. This structure supplies
neither a complete native event trace nor any successful run witness. -/
structure Callees where
  op19_OPEN : PV_EVH_Prefix.P (std.fs.OpenOptions)
  op20_OPEN : ∀ (arg0 : std.fs.OpenOptions) (arg1 : Bool), PV_EVH_Prefix.P ((std.fs.OpenOptions × (std.fs.OpenOptions → std.fs.OpenOptions)))
  op21_OPEN : ∀ (arg0 : std.fs.OpenOptions) (arg1 : Bool), PV_EVH_Prefix.P ((std.fs.OpenOptions × (std.fs.OpenOptions → std.fs.OpenOptions)))
  op24_OPEN : ∀ (arg0 : std.fs.OpenOptions) (arg1 : Std.U32), PV_EVH_Prefix.P ((std.fs.OpenOptions × (std.fs.OpenOptions → std.fs.OpenOptions)))
  op25_OPEN : ∀ (arg0 : std.path.PathBuf), PV_EVH_Prefix.P (std.path.Path)
  op23_OPEN : ∀ (arg0 : std.io.error.Error), PV_EVH_Prefix.P (core.io.error.ErrorKind)
  op2_OPEN : ∀ (arg0 : core.io.error.ErrorKind) (arg1 : core.io.error.ErrorKind), PV_EVH_Prefix.P (Bool)

structure Compatible (c : Callees) : Prop where
  op19_fixed : FinishedView (c.op19_OPEN) (std.fs.OpenOptions.new)
  op20_fixed : ∀ (arg0 : std.fs.OpenOptions) (arg1 : Bool), FinishedView (c.op20_OPEN arg0 arg1) (std.fs.OpenOptions.write arg0 arg1)
  op21_fixed : ∀ (arg0 : std.fs.OpenOptions) (arg1 : Bool), FinishedView (c.op21_OPEN arg0 arg1) (std.fs.OpenOptions.create_new arg0 arg1)
  op24_fixed : ∀ (arg0 : std.fs.OpenOptions) (arg1 : Std.U32), FinishedView (c.op24_OPEN arg0 arg1) (std.fs.OpenOptions.Insts.StdOsUnixFsOpenOptionsExt.mode arg0 arg1)
  op25_fixed : ∀ (arg0 : std.path.PathBuf), FinishedView (c.op25_OPEN arg0) (std.path.PathBuf.Insts.CoreOpsDerefDerefPath.deref arg0)
  op23_fixed : ∀ (arg0 : std.io.error.Error), FinishedView (c.op23_OPEN arg0) (std.io.error.Error.kind arg0)
  op2_fixed : ∀ (arg0 : core.io.error.ErrorKind) (arg1 : core.io.error.ErrorKind), FinishedView (c.op2_OPEN arg0 arg1) (core.io.error.ErrorKind.Insts.CoreCmpPartialEqErrorKind.eq arg0 arg1)

def run
  (self : aspis_prover.state_only_entropy.DurableStateOnlyMaskNonceStore)
  (statement_digest : Array Std.U8 32#usize)
  (mask_nonce : Array Std.U8 32#usize) (fileAnswers : PV_EVH_NonceWorld.Answers) (pathCallees : PV_EVH_NoncePath.Callees) (c : Callees) : PV_EVH_Prefix.P ((core.result.Result Bool std.io.error.Error) ×
    aspis_prover.state_only_entropy.DurableStateOnlyMaskNonceStore) := do
  let path ← PV_EVH_NoncePath.run { self with last_error := none } mask_nonce pathCallees
  let options ← c.op19_OPEN
  let (oo, write_back) ← c.op20_OPEN options true
  let (oo1, create_new_back) ← c.op21_OPEN oo true
  let oo2 := create_new_back oo1
  let options1 := write_back oo2
  let (oo3, mode_back) ← c.op24_OPEN options1 384#u32
  let options2 := mode_back oo3
  let r ← PV_EVH_Prefix.ofM (PV_EVH_NonceWorld.optionsOpen fileAnswers std.path.PathBuf.Insts.CoreConvertAsRefPath options2 path)
  match r with
  | core.result.Result.Ok file =>
    let s ← PV_EVH_Prefix.lift (Aeneas.Std.lift (Array.to_slice aspis_prover.state_only_entropy.RESERVATION_MAGIC))
    let (r1, file1) ← PV_EVH_Prefix.ofM (PV_EVH_NonceWorld.writeAll fileAnswers file s)
    let cf ← PV_EVH_Prefix.lift (core.result.Result.Insts.CoreOpsTry.branch r1)
    match cf with
    | core.ops.control_flow.ControlFlow.Continue _ =>
      let s1 ← PV_EVH_Prefix.lift (Aeneas.Std.lift (Array.to_slice statement_digest))
      let (r2, file2) ← PV_EVH_Prefix.ofM (PV_EVH_NonceWorld.writeAll fileAnswers file1 s1)
      let cf1 ← PV_EVH_Prefix.lift (core.result.Result.Insts.CoreOpsTry.branch r2)
      match cf1 with
      | core.ops.control_flow.ControlFlow.Continue _ =>
        let s2 ← PV_EVH_Prefix.lift (Aeneas.Std.lift (Array.to_slice mask_nonce))
        let (r3, file3) ← PV_EVH_Prefix.ofM (PV_EVH_NonceWorld.writeAll fileAnswers file2 s2)
        let cf2 ← PV_EVH_Prefix.lift (core.result.Result.Insts.CoreOpsTry.branch r3)
        match cf2 with
        | core.ops.control_flow.ControlFlow.Continue _ =>
          let r4 ← PV_EVH_Prefix.ofM (PV_EVH_NonceWorld.sync fileAnswers file3)
          let cf3 ← PV_EVH_Prefix.lift (core.result.Result.Insts.CoreOpsTry.branch r4)
          match cf3 with
          | core.ops.control_flow.ControlFlow.Continue _ =>
            let p ← c.op25_OPEN self.directory
            let r5 ← PV_EVH_SyncDirectory.run p fileAnswers {}
            let cf4 ← PV_EVH_Prefix.lift (core.result.Result.Insts.CoreOpsTry.branch r5)
            match cf4 with
            | core.ops.control_flow.ControlFlow.Continue _ =>
              pure (core.result.Result.Ok true, { self with last_error := none })
            | core.ops.control_flow.ControlFlow.Break residual =>
              let r6 ← PV_EVH_Prefix.lift (core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
                  Bool (core.convert.FromSame std.io.error.Error) residual)
              pure (r6, { self with last_error := none })
          | core.ops.control_flow.ControlFlow.Break residual =>
            let r5 ← PV_EVH_Prefix.lift (core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
                Bool (core.convert.FromSame std.io.error.Error) residual)
            pure (r5, { self with last_error := none })
        | core.ops.control_flow.ControlFlow.Break residual =>
          let r4 ← PV_EVH_Prefix.lift (core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
              Bool (core.convert.FromSame std.io.error.Error) residual)
          pure (r4, { self with last_error := none })
      | core.ops.control_flow.ControlFlow.Break residual =>
        let r3 ← PV_EVH_Prefix.lift (core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
            Bool (core.convert.FromSame std.io.error.Error) residual)
        pure (r3, { self with last_error := none })
    | core.ops.control_flow.ControlFlow.Break residual =>
      let r2 ← PV_EVH_Prefix.lift (core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
          Bool (core.convert.FromSame std.io.error.Error) residual)
      pure (r2, { self with last_error := none })
  | core.result.Result.Err error =>
    let ek ← c.op23_OPEN error
    let b ← c.op2_OPEN ek
        core.io.error.ErrorKind.AlreadyExists
    let r1 ← if b then
        pure (core.result.Result.Ok false)
      else
        pure (core.result.Result.Err error)
    pure (r1, { self with last_error := none })

theorem run_fixed
  (self : aspis_prover.state_only_entropy.DurableStateOnlyMaskNonceStore)
  (statement_digest : Array Std.U8 32#usize)
  (mask_nonce : Array Std.U8 32#usize) (fileAnswers : PV_EVH_NonceWorld.Answers) (pathCallees : PV_EVH_NoncePath.Callees) (c : Callees) (compatible : Compatible c) (files_same : PV_EVH_NonceWorld.Compatible fileAnswers) (path_same : PV_EVH_NoncePath.Compatible pathCallees) :
    FinishedView (run self statement_digest mask_nonce fileAnswers pathCallees c) (aspis_prover.state_only_entropy.DurableStateOnlyMaskNonceStore.reserve_fallible self statement_digest mask_nonce) := by
  unfold run aspis_prover.state_only_entropy.DurableStateOnlyMaskNonceStore.reserve_fallible
  try dsimp only
  apply PV_EVH_Prefix.bind_fixed
  ·
    exact PV_EVH_NoncePath.run_fixed _ _ pathCallees path_same
  · intro path
    try dsimp only
    apply PV_EVH_Prefix.bind_fixed
    ·
      exact compatible.op19_fixed
    · intro options
      try dsimp only
      apply PV_EVH_Prefix.bind_fixed
      ·
        exact compatible.op20_fixed _ _
      · rintro ⟨oo, write_back⟩
        try dsimp only
        apply PV_EVH_Prefix.bind_fixed
        ·
          exact compatible.op21_fixed _ _
        · rintro ⟨oo1, create_new_back⟩
          let oo2 := create_new_back oo1
          try dsimp only
          let options1 := write_back oo2
          try dsimp only
          try dsimp only
          apply PV_EVH_Prefix.bind_fixed
          ·
            exact compatible.op24_fixed _ _
          · rintro ⟨oo3, mode_back⟩
            let options2 := mode_back oo3
            try dsimp only
            try dsimp only
            apply PV_EVH_Prefix.bind_fixed
            ·
              exact PV_EVH_Prefix.ofM_fixed _ _ (PV_EVH_NonceWorld.options_fixed fileAnswers _ _ _ (fun w => files_same.options _ _ _ w))
            · intro r
              try dsimp only
              cases r with
              | Ok file =>
                try dsimp only
                apply PV_EVH_Prefix.bind_fixed
                ·
                  exact PV_EVH_Prefix.lift_fixed _
                · intro s
                  try dsimp only
                  apply PV_EVH_Prefix.bind_fixed
                  ·
                    exact PV_EVH_Prefix.ofM_fixed _ _ (PV_EVH_NonceWorld.write_fixed fileAnswers _ _ (fun w => files_same.write w _ _))
                  · rintro ⟨r1, file1⟩
                    try dsimp only
                    apply PV_EVH_Prefix.bind_fixed
                    ·
                      exact PV_EVH_Prefix.lift_fixed _
                    · intro cf
                      try dsimp only
                      cases cf with
                      | Continue unused0 =>
                        try dsimp only
                        apply PV_EVH_Prefix.bind_fixed
                        ·
                          exact PV_EVH_Prefix.lift_fixed _
                        · intro s1
                          try dsimp only
                          apply PV_EVH_Prefix.bind_fixed
                          ·
                            exact PV_EVH_Prefix.ofM_fixed _ _ (PV_EVH_NonceWorld.write_fixed fileAnswers _ _ (fun w => files_same.write w _ _))
                          · rintro ⟨r2, file2⟩
                            try dsimp only
                            apply PV_EVH_Prefix.bind_fixed
                            ·
                              exact PV_EVH_Prefix.lift_fixed _
                            · intro cf1
                              try dsimp only
                              cases cf1 with
                              | Continue unused0 =>
                                try dsimp only
                                apply PV_EVH_Prefix.bind_fixed
                                ·
                                  exact PV_EVH_Prefix.lift_fixed _
                                · intro s2
                                  try dsimp only
                                  apply PV_EVH_Prefix.bind_fixed
                                  ·
                                    exact PV_EVH_Prefix.ofM_fixed _ _ (PV_EVH_NonceWorld.write_fixed fileAnswers _ _ (fun w => files_same.write w _ _))
                                  · rintro ⟨r3, file3⟩
                                    try dsimp only
                                    apply PV_EVH_Prefix.bind_fixed
                                    ·
                                      exact PV_EVH_Prefix.lift_fixed _
                                    · intro cf2
                                      try dsimp only
                                      cases cf2 with
                                      | Continue unused0 =>
                                        try dsimp only
                                        apply PV_EVH_Prefix.bind_fixed
                                        ·
                                          exact PV_EVH_Prefix.ofM_fixed _ _ (PV_EVH_NonceWorld.sync_fixed fileAnswers _ (fun w => files_same.sync w _))
                                        · intro r4
                                          try dsimp only
                                          apply PV_EVH_Prefix.bind_fixed
                                          ·
                                            exact PV_EVH_Prefix.lift_fixed _
                                          · intro cf3
                                            try dsimp only
                                            cases cf3 with
                                            | Continue unused0 =>
                                              try dsimp only
                                              apply PV_EVH_Prefix.bind_fixed
                                              ·
                                                exact compatible.op25_fixed _
                                              · intro p
                                                try dsimp only
                                                apply PV_EVH_Prefix.bind_fixed
                                                ·
                                                  exact PV_EVH_SyncDirectory.run_fixed _ fileAnswers {} {} files_same
                                                · intro r5
                                                  try dsimp only
                                                  apply PV_EVH_Prefix.bind_fixed
                                                  ·
                                                    exact PV_EVH_Prefix.lift_fixed _
                                                  · intro cf4
                                                    try dsimp only
                                                    cases cf4 with
                                                    | Continue unused0 =>
                                                      exact PV_EVH_Prefix.lift_fixed _
                                                    | Break residual =>
                                                      try dsimp only
                                                      apply PV_EVH_Prefix.bind_fixed
                                                      ·
                                                        exact PV_EVH_Prefix.lift_fixed _
                                                      · intro r6
                                                        exact PV_EVH_Prefix.lift_fixed _
                                            | Break residual =>
                                              try dsimp only
                                              apply PV_EVH_Prefix.bind_fixed
                                              ·
                                                exact PV_EVH_Prefix.lift_fixed _
                                              · intro r5
                                                exact PV_EVH_Prefix.lift_fixed _
                                      | Break residual =>
                                        try dsimp only
                                        apply PV_EVH_Prefix.bind_fixed
                                        ·
                                          exact PV_EVH_Prefix.lift_fixed _
                                        · intro r4
                                          exact PV_EVH_Prefix.lift_fixed _
                              | Break residual =>
                                try dsimp only
                                apply PV_EVH_Prefix.bind_fixed
                                ·
                                  exact PV_EVH_Prefix.lift_fixed _
                                · intro r3
                                  exact PV_EVH_Prefix.lift_fixed _
                      | Break residual =>
                        try dsimp only
                        apply PV_EVH_Prefix.bind_fixed
                        ·
                          exact PV_EVH_Prefix.lift_fixed _
                        · intro r2
                          exact PV_EVH_Prefix.lift_fixed _
              | Err error =>
                try dsimp only
                apply PV_EVH_Prefix.bind_fixed
                ·
                  exact compatible.op23_fixed _
                · intro ek
                  try dsimp only
                  apply PV_EVH_Prefix.bind_fixed
                  ·
                    exact compatible.op2_fixed _ _
                  · intro b
                    try dsimp only
                    apply PV_EVH_Prefix.bind_fixed
                    ·
                      by_cases condition : b
                      · try dsimp only [oo2,options1,options2] at condition
                        simp only [condition,if_true]
                        exact PV_EVH_Prefix.lift_fixed _
                      · try dsimp only [oo2,options1,options2] at condition
                        simp only [condition,if_false]
                        exact PV_EVH_Prefix.lift_fixed _
                    · intro r1
                      exact PV_EVH_Prefix.lift_fixed _

#print axioms run_fixed
end PV_EVH_NonceReserveFallible
