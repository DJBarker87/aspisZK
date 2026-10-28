import AspisR1TerminalDecoder.Funs
import R1Z.PV_W_IfLaws
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RJDec_Parser03
open Aeneas Aeneas.Std AspisR1TerminalDecoder PV_W_TypedEffects PV_W_RecursiveLaws
variable [ProverRwFull.ExternalTypes]

def program
  (bytes : Array Std.U8 32#usize) :
  P (core.result.Result (Array aspis_core.field.M31 8#usize) atomic_statement.AtomicStatementError) := do
  let i ← invoke "Array.index_usize" (fun ops =>
      letI : ProverRwFull.ExternalFuns := ops
      Array.index_usize bytes 0#usize)
  let i1 ← invoke "Array.index_usize" (fun ops =>
      letI : ProverRwFull.ExternalFuns := ops
      Array.index_usize bytes 1#usize)
  let i2 ← invoke "Array.index_usize" (fun ops =>
      letI : ProverRwFull.ExternalFuns := ops
      Array.index_usize bytes 2#usize)
  let i3 ← invoke "Array.index_usize" (fun ops =>
      letI : ProverRwFull.ExternalFuns := ops
      Array.index_usize bytes 3#usize)
  let o ← invoke "aspis_core.field.M31.from_le_bytes" (fun ops =>
      letI : ProverRwFull.ExternalFuns := ops
      aspis_core.field.M31.from_le_bytes (Array.make 4#usize [ i, i1, i2, i3 ]))
  let r ← invoke "core.option.Option.ok_or" (fun ops =>
      letI : ProverRwFull.ExternalFuns := ops
      core.option.Option.ok_or o atomic_statement.AtomicStatementError.NonCanonicalDigest)
  let cf ← invoke "core.result.Result.Insts.CoreOpsTry.branch" (fun ops =>
      letI : ProverRwFull.ExternalFuns := ops
      core.result.Result.Insts.CoreOpsTry.branch r)
  match cf with
  | core.ops.control_flow.ControlFlow.Continue val =>
    let i4 ← invoke "Array.index_usize" (fun ops =>
        letI : ProverRwFull.ExternalFuns := ops
        Array.index_usize bytes 4#usize)
    let i5 ← invoke "Array.index_usize" (fun ops =>
        letI : ProverRwFull.ExternalFuns := ops
        Array.index_usize bytes 5#usize)
    let i6 ← invoke "Array.index_usize" (fun ops =>
        letI : ProverRwFull.ExternalFuns := ops
        Array.index_usize bytes 6#usize)
    let i7 ← invoke "Array.index_usize" (fun ops =>
        letI : ProverRwFull.ExternalFuns := ops
        Array.index_usize bytes 7#usize)
    let o1 ← invoke "aspis_core.field.M31.from_le_bytes" (fun ops =>
        letI : ProverRwFull.ExternalFuns := ops
        aspis_core.field.M31.from_le_bytes (Array.make 4#usize [ i4, i5, i6, i7 ]))
    let r1 ← invoke "core.option.Option.ok_or" (fun ops =>
        letI : ProverRwFull.ExternalFuns := ops
        core.option.Option.ok_or o1 atomic_statement.AtomicStatementError.NonCanonicalDigest)
    let cf1 ← invoke "core.result.Result.Insts.CoreOpsTry.branch" (fun ops =>
        letI : ProverRwFull.ExternalFuns := ops
        core.result.Result.Insts.CoreOpsTry.branch r1)
    match cf1 with
    | core.ops.control_flow.ControlFlow.Continue val1 =>
      let i8 ← invoke "Array.index_usize" (fun ops =>
          letI : ProverRwFull.ExternalFuns := ops
          Array.index_usize bytes 8#usize)
      let i9 ← invoke "Array.index_usize" (fun ops =>
          letI : ProverRwFull.ExternalFuns := ops
          Array.index_usize bytes 9#usize)
      let i10 ← invoke "Array.index_usize" (fun ops =>
          letI : ProverRwFull.ExternalFuns := ops
          Array.index_usize bytes 10#usize)
      let i11 ← invoke "Array.index_usize" (fun ops =>
          letI : ProverRwFull.ExternalFuns := ops
          Array.index_usize bytes 11#usize)
      let o2 ← invoke "aspis_core.field.M31.from_le_bytes" (fun ops =>
          letI : ProverRwFull.ExternalFuns := ops
          aspis_core.field.M31.from_le_bytes (Array.make 4#usize [ i8, i9, i10, i11 ]))
      let r2 ← invoke "core.option.Option.ok_or" (fun ops =>
          letI : ProverRwFull.ExternalFuns := ops
          core.option.Option.ok_or o2 atomic_statement.AtomicStatementError.NonCanonicalDigest)
      let cf2 ← invoke "core.result.Result.Insts.CoreOpsTry.branch" (fun ops =>
          letI : ProverRwFull.ExternalFuns := ops
          core.result.Result.Insts.CoreOpsTry.branch r2)
      match cf2 with
      | core.ops.control_flow.ControlFlow.Continue val2 =>
        let i12 ← invoke "Array.index_usize" (fun ops =>
            letI : ProverRwFull.ExternalFuns := ops
            Array.index_usize bytes 12#usize)
        let i13 ← invoke "Array.index_usize" (fun ops =>
            letI : ProverRwFull.ExternalFuns := ops
            Array.index_usize bytes 13#usize)
        let i14 ← invoke "Array.index_usize" (fun ops =>
            letI : ProverRwFull.ExternalFuns := ops
            Array.index_usize bytes 14#usize)
        let i15 ← invoke "Array.index_usize" (fun ops =>
            letI : ProverRwFull.ExternalFuns := ops
            Array.index_usize bytes 15#usize)
        let o3 ← invoke "aspis_core.field.M31.from_le_bytes" (fun ops =>
            letI : ProverRwFull.ExternalFuns := ops
            aspis_core.field.M31.from_le_bytes (Array.make 4#usize [ i12, i13, i14, i15 ]))
        let r3 ← invoke "core.option.Option.ok_or" (fun ops =>
            letI : ProverRwFull.ExternalFuns := ops
            core.option.Option.ok_or o3 atomic_statement.AtomicStatementError.NonCanonicalDigest)
        let cf3 ← invoke "core.result.Result.Insts.CoreOpsTry.branch" (fun ops =>
            letI : ProverRwFull.ExternalFuns := ops
            core.result.Result.Insts.CoreOpsTry.branch r3)
        match cf3 with
        | core.ops.control_flow.ControlFlow.Continue val3 =>
          let i16 ← invoke "Array.index_usize" (fun ops =>
              letI : ProverRwFull.ExternalFuns := ops
              Array.index_usize bytes 16#usize)
          let i17 ← invoke "Array.index_usize" (fun ops =>
              letI : ProverRwFull.ExternalFuns := ops
              Array.index_usize bytes 17#usize)
          let i18 ← invoke "Array.index_usize" (fun ops =>
              letI : ProverRwFull.ExternalFuns := ops
              Array.index_usize bytes 18#usize)
          let i19 ← invoke "Array.index_usize" (fun ops =>
              letI : ProverRwFull.ExternalFuns := ops
              Array.index_usize bytes 19#usize)
          let o4 ← invoke "aspis_core.field.M31.from_le_bytes" (fun ops =>
              letI : ProverRwFull.ExternalFuns := ops
              aspis_core.field.M31.from_le_bytes (Array.make 4#usize [ i16, i17, i18, i19 ]))
          let r4 ← invoke "core.option.Option.ok_or" (fun ops =>
              letI : ProverRwFull.ExternalFuns := ops
              core.option.Option.ok_or o4 atomic_statement.AtomicStatementError.NonCanonicalDigest)
          let cf4 ← invoke "core.result.Result.Insts.CoreOpsTry.branch" (fun ops =>
              letI : ProverRwFull.ExternalFuns := ops
              core.result.Result.Insts.CoreOpsTry.branch r4)
          match cf4 with
          | core.ops.control_flow.ControlFlow.Continue val4 =>
            let i20 ← invoke "Array.index_usize" (fun ops =>
                letI : ProverRwFull.ExternalFuns := ops
                Array.index_usize bytes 20#usize)
            let i21 ← invoke "Array.index_usize" (fun ops =>
                letI : ProverRwFull.ExternalFuns := ops
                Array.index_usize bytes 21#usize)
            let i22 ← invoke "Array.index_usize" (fun ops =>
                letI : ProverRwFull.ExternalFuns := ops
                Array.index_usize bytes 22#usize)
            let i23 ← invoke "Array.index_usize" (fun ops =>
                letI : ProverRwFull.ExternalFuns := ops
                Array.index_usize bytes 23#usize)
            let o5 ← invoke "aspis_core.field.M31.from_le_bytes" (fun ops =>
                letI : ProverRwFull.ExternalFuns := ops
                aspis_core.field.M31.from_le_bytes (Array.make 4#usize [ i20, i21, i22, i23 ]))
            let r5 ← invoke "core.option.Option.ok_or" (fun ops =>
                letI : ProverRwFull.ExternalFuns := ops
                core.option.Option.ok_or o5 atomic_statement.AtomicStatementError.NonCanonicalDigest)
            let cf5 ← invoke "core.result.Result.Insts.CoreOpsTry.branch" (fun ops =>
                letI : ProverRwFull.ExternalFuns := ops
                core.result.Result.Insts.CoreOpsTry.branch r5)
            match cf5 with
            | core.ops.control_flow.ControlFlow.Continue val5 =>
              let i24 ← invoke "Array.index_usize" (fun ops =>
                  letI : ProverRwFull.ExternalFuns := ops
                  Array.index_usize bytes 24#usize)
              let i25 ← invoke "Array.index_usize" (fun ops =>
                  letI : ProverRwFull.ExternalFuns := ops
                  Array.index_usize bytes 25#usize)
              let i26 ← invoke "Array.index_usize" (fun ops =>
                  letI : ProverRwFull.ExternalFuns := ops
                  Array.index_usize bytes 26#usize)
              let i27 ← invoke "Array.index_usize" (fun ops =>
                  letI : ProverRwFull.ExternalFuns := ops
                  Array.index_usize bytes 27#usize)
              let o6 ← invoke "aspis_core.field.M31.from_le_bytes" (fun ops =>
                  letI : ProverRwFull.ExternalFuns := ops
                  aspis_core.field.M31.from_le_bytes (Array.make 4#usize [ i24, i25, i26, i27 ]))
              let r6 ← invoke "core.option.Option.ok_or" (fun ops =>
                  letI : ProverRwFull.ExternalFuns := ops
                  core.option.Option.ok_or o6 atomic_statement.AtomicStatementError.NonCanonicalDigest)
              let cf6 ← invoke "core.result.Result.Insts.CoreOpsTry.branch" (fun ops =>
                  letI : ProverRwFull.ExternalFuns := ops
                  core.result.Result.Insts.CoreOpsTry.branch r6)
              match cf6 with
              | core.ops.control_flow.ControlFlow.Continue val6 =>
                let i28 ← invoke "Array.index_usize" (fun ops =>
                    letI : ProverRwFull.ExternalFuns := ops
                    Array.index_usize bytes 28#usize)
                let i29 ← invoke "Array.index_usize" (fun ops =>
                    letI : ProverRwFull.ExternalFuns := ops
                    Array.index_usize bytes 29#usize)
                let i30 ← invoke "Array.index_usize" (fun ops =>
                    letI : ProverRwFull.ExternalFuns := ops
                    Array.index_usize bytes 30#usize)
                let i31 ← invoke "Array.index_usize" (fun ops =>
                    letI : ProverRwFull.ExternalFuns := ops
                    Array.index_usize bytes 31#usize)
                let o7 ← invoke "aspis_core.field.M31.from_le_bytes" (fun ops =>
                    letI : ProverRwFull.ExternalFuns := ops
                    aspis_core.field.M31.from_le_bytes (Array.make 4#usize [ i28, i29, i30, i31 ]))
                let r7 ← invoke "core.option.Option.ok_or" (fun ops =>
                    letI : ProverRwFull.ExternalFuns := ops
                    core.option.Option.ok_or o7 atomic_statement.AtomicStatementError.NonCanonicalDigest)
                let cf7 ← invoke "core.result.Result.Insts.CoreOpsTry.branch" (fun ops =>
                    letI : ProverRwFull.ExternalFuns := ops
                    core.result.Result.Insts.CoreOpsTry.branch r7)
                match cf7 with
                | core.ops.control_flow.ControlFlow.Continue val7 =>
                  pure (core.result.Result.Ok (Array.make 8#usize [ val, val1, val2, val3, val4, val5, val6, val7 ]))
                | core.ops.control_flow.ControlFlow.Break residual =>
                  invoke "core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual" (fun ops =>
                    letI : ProverRwFull.ExternalFuns := ops
                    core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual (Array aspis_core.field.M31 8#usize) (core.convert.FromSame atomic_statement.AtomicStatementError) residual)
              | core.ops.control_flow.ControlFlow.Break residual =>
                invoke "core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual" (fun ops =>
                  letI : ProverRwFull.ExternalFuns := ops
                  core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual (Array aspis_core.field.M31 8#usize) (core.convert.FromSame atomic_statement.AtomicStatementError) residual)
            | core.ops.control_flow.ControlFlow.Break residual =>
              invoke "core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual" (fun ops =>
                letI : ProverRwFull.ExternalFuns := ops
                core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual (Array aspis_core.field.M31 8#usize) (core.convert.FromSame atomic_statement.AtomicStatementError) residual)
          | core.ops.control_flow.ControlFlow.Break residual =>
            invoke "core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual" (fun ops =>
              letI : ProverRwFull.ExternalFuns := ops
              core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual (Array aspis_core.field.M31 8#usize) (core.convert.FromSame atomic_statement.AtomicStatementError) residual)
        | core.ops.control_flow.ControlFlow.Break residual =>
          invoke "core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual" (fun ops =>
            letI : ProverRwFull.ExternalFuns := ops
            core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual (Array aspis_core.field.M31 8#usize) (core.convert.FromSame atomic_statement.AtomicStatementError) residual)
      | core.ops.control_flow.ControlFlow.Break residual =>
        invoke "core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual" (fun ops =>
          letI : ProverRwFull.ExternalFuns := ops
          core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual (Array aspis_core.field.M31 8#usize) (core.convert.FromSame atomic_statement.AtomicStatementError) residual)
    | core.ops.control_flow.ControlFlow.Break residual =>
      invoke "core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual" (fun ops =>
        letI : ProverRwFull.ExternalFuns := ops
        core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual (Array aspis_core.field.M31 8#usize) (core.convert.FromSame atomic_statement.AtomicStatementError) residual)
  | core.ops.control_flow.ControlFlow.Break residual =>
    invoke "core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual" (fun ops =>
      letI : ProverRwFull.ExternalFuns := ops
      core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual (Array aspis_core.field.M31 8#usize) (core.convert.FromSame atomic_statement.AtomicStatementError) residual)

theorem source (ops : ProverRwFull.ExternalFuns)
  (bytes : Array Std.U8 32#usize) :
  erase ops (program bytes) =
    atomic_statement.decode_digest_canonical bytes := by
  unfold program atomic_statement.decode_digest_canonical
  try dsimp only
  rw [erase_bind]
  apply PV_W_RecursiveLaws.bind_congr
  ·
    exact erase_invoke ops _ _
  · intro i
    try dsimp only
    rw [erase_bind]
    apply PV_W_RecursiveLaws.bind_congr
    ·
      exact erase_invoke ops _ _
    · intro i1
      try dsimp only
      rw [erase_bind]
      apply PV_W_RecursiveLaws.bind_congr
      ·
        exact erase_invoke ops _ _
      · intro i2
        try dsimp only
        rw [erase_bind]
        apply PV_W_RecursiveLaws.bind_congr
        ·
          exact erase_invoke ops _ _
        · intro i3
          try dsimp only
          rw [erase_bind]
          apply PV_W_RecursiveLaws.bind_congr
          ·
            exact erase_invoke ops _ _
          · intro o
            try dsimp only
            rw [erase_bind]
            apply PV_W_RecursiveLaws.bind_congr
            ·
              exact erase_invoke ops _ _
            · intro r
              try dsimp only
              rw [erase_bind]
              apply PV_W_RecursiveLaws.bind_congr
              ·
                exact erase_invoke ops _ _
              · intro cf
                try dsimp only
                cases cf with
                | Continue val =>
                  try dsimp only
                  rw [erase_bind]
                  apply PV_W_RecursiveLaws.bind_congr
                  ·
                    exact erase_invoke ops _ _
                  · intro i4
                    try dsimp only
                    rw [erase_bind]
                    apply PV_W_RecursiveLaws.bind_congr
                    ·
                      exact erase_invoke ops _ _
                    · intro i5
                      try dsimp only
                      rw [erase_bind]
                      apply PV_W_RecursiveLaws.bind_congr
                      ·
                        exact erase_invoke ops _ _
                      · intro i6
                        try dsimp only
                        rw [erase_bind]
                        apply PV_W_RecursiveLaws.bind_congr
                        ·
                          exact erase_invoke ops _ _
                        · intro i7
                          try dsimp only
                          rw [erase_bind]
                          apply PV_W_RecursiveLaws.bind_congr
                          ·
                            exact erase_invoke ops _ _
                          · intro o1
                            try dsimp only
                            rw [erase_bind]
                            apply PV_W_RecursiveLaws.bind_congr
                            ·
                              exact erase_invoke ops _ _
                            · intro r1
                              try dsimp only
                              rw [erase_bind]
                              apply PV_W_RecursiveLaws.bind_congr
                              ·
                                exact erase_invoke ops _ _
                              · intro cf1
                                try dsimp only
                                cases cf1 with
                                | Continue val1 =>
                                  try dsimp only
                                  rw [erase_bind]
                                  apply PV_W_RecursiveLaws.bind_congr
                                  ·
                                    exact erase_invoke ops _ _
                                  · intro i8
                                    try dsimp only
                                    rw [erase_bind]
                                    apply PV_W_RecursiveLaws.bind_congr
                                    ·
                                      exact erase_invoke ops _ _
                                    · intro i9
                                      try dsimp only
                                      rw [erase_bind]
                                      apply PV_W_RecursiveLaws.bind_congr
                                      ·
                                        exact erase_invoke ops _ _
                                      · intro i10
                                        try dsimp only
                                        rw [erase_bind]
                                        apply PV_W_RecursiveLaws.bind_congr
                                        ·
                                          exact erase_invoke ops _ _
                                        · intro i11
                                          try dsimp only
                                          rw [erase_bind]
                                          apply PV_W_RecursiveLaws.bind_congr
                                          ·
                                            exact erase_invoke ops _ _
                                          · intro o2
                                            try dsimp only
                                            rw [erase_bind]
                                            apply PV_W_RecursiveLaws.bind_congr
                                            ·
                                              exact erase_invoke ops _ _
                                            · intro r2
                                              try dsimp only
                                              rw [erase_bind]
                                              apply PV_W_RecursiveLaws.bind_congr
                                              ·
                                                exact erase_invoke ops _ _
                                              · intro cf2
                                                try dsimp only
                                                cases cf2 with
                                                | Continue val2 =>
                                                  try dsimp only
                                                  rw [erase_bind]
                                                  apply PV_W_RecursiveLaws.bind_congr
                                                  ·
                                                    exact erase_invoke ops _ _
                                                  · intro i12
                                                    try dsimp only
                                                    rw [erase_bind]
                                                    apply PV_W_RecursiveLaws.bind_congr
                                                    ·
                                                      exact erase_invoke ops _ _
                                                    · intro i13
                                                      try dsimp only
                                                      rw [erase_bind]
                                                      apply PV_W_RecursiveLaws.bind_congr
                                                      ·
                                                        exact erase_invoke ops _ _
                                                      · intro i14
                                                        try dsimp only
                                                        rw [erase_bind]
                                                        apply PV_W_RecursiveLaws.bind_congr
                                                        ·
                                                          exact erase_invoke ops _ _
                                                        · intro i15
                                                          try dsimp only
                                                          rw [erase_bind]
                                                          apply PV_W_RecursiveLaws.bind_congr
                                                          ·
                                                            exact erase_invoke ops _ _
                                                          · intro o3
                                                            try dsimp only
                                                            rw [erase_bind]
                                                            apply PV_W_RecursiveLaws.bind_congr
                                                            ·
                                                              exact erase_invoke ops _ _
                                                            · intro r3
                                                              try dsimp only
                                                              rw [erase_bind]
                                                              apply PV_W_RecursiveLaws.bind_congr
                                                              ·
                                                                exact erase_invoke ops _ _
                                                              · intro cf3
                                                                try dsimp only
                                                                cases cf3 with
                                                                | Continue val3 =>
                                                                  try dsimp only
                                                                  rw [erase_bind]
                                                                  apply PV_W_RecursiveLaws.bind_congr
                                                                  ·
                                                                    exact erase_invoke ops _ _
                                                                  · intro i16
                                                                    try dsimp only
                                                                    rw [erase_bind]
                                                                    apply PV_W_RecursiveLaws.bind_congr
                                                                    ·
                                                                      exact erase_invoke ops _ _
                                                                    · intro i17
                                                                      try dsimp only
                                                                      rw [erase_bind]
                                                                      apply PV_W_RecursiveLaws.bind_congr
                                                                      ·
                                                                        exact erase_invoke ops _ _
                                                                      · intro i18
                                                                        try dsimp only
                                                                        rw [erase_bind]
                                                                        apply PV_W_RecursiveLaws.bind_congr
                                                                        ·
                                                                          exact erase_invoke ops _ _
                                                                        · intro i19
                                                                          try dsimp only
                                                                          rw [erase_bind]
                                                                          apply PV_W_RecursiveLaws.bind_congr
                                                                          ·
                                                                            exact erase_invoke ops _ _
                                                                          · intro o4
                                                                            try dsimp only
                                                                            rw [erase_bind]
                                                                            apply PV_W_RecursiveLaws.bind_congr
                                                                            ·
                                                                              exact erase_invoke ops _ _
                                                                            · intro r4
                                                                              try dsimp only
                                                                              rw [erase_bind]
                                                                              apply PV_W_RecursiveLaws.bind_congr
                                                                              ·
                                                                                exact erase_invoke ops _ _
                                                                              · intro cf4
                                                                                try dsimp only
                                                                                cases cf4 with
                                                                                | Continue val4 =>
                                                                                  try dsimp only
                                                                                  rw [erase_bind]
                                                                                  apply PV_W_RecursiveLaws.bind_congr
                                                                                  ·
                                                                                    exact erase_invoke ops _ _
                                                                                  · intro i20
                                                                                    try dsimp only
                                                                                    rw [erase_bind]
                                                                                    apply PV_W_RecursiveLaws.bind_congr
                                                                                    ·
                                                                                      exact erase_invoke ops _ _
                                                                                    · intro i21
                                                                                      try dsimp only
                                                                                      rw [erase_bind]
                                                                                      apply PV_W_RecursiveLaws.bind_congr
                                                                                      ·
                                                                                        exact erase_invoke ops _ _
                                                                                      · intro i22
                                                                                        try dsimp only
                                                                                        rw [erase_bind]
                                                                                        apply PV_W_RecursiveLaws.bind_congr
                                                                                        ·
                                                                                          exact erase_invoke ops _ _
                                                                                        · intro i23
                                                                                          try dsimp only
                                                                                          rw [erase_bind]
                                                                                          apply PV_W_RecursiveLaws.bind_congr
                                                                                          ·
                                                                                            exact erase_invoke ops _ _
                                                                                          · intro o5
                                                                                            try dsimp only
                                                                                            rw [erase_bind]
                                                                                            apply PV_W_RecursiveLaws.bind_congr
                                                                                            ·
                                                                                              exact erase_invoke ops _ _
                                                                                            · intro r5
                                                                                              try dsimp only
                                                                                              rw [erase_bind]
                                                                                              apply PV_W_RecursiveLaws.bind_congr
                                                                                              ·
                                                                                                exact erase_invoke ops _ _
                                                                                              · intro cf5
                                                                                                try dsimp only
                                                                                                cases cf5 with
                                                                                                | Continue val5 =>
                                                                                                  try dsimp only
                                                                                                  rw [erase_bind]
                                                                                                  apply PV_W_RecursiveLaws.bind_congr
                                                                                                  ·
                                                                                                    exact erase_invoke ops _ _
                                                                                                  · intro i24
                                                                                                    try dsimp only
                                                                                                    rw [erase_bind]
                                                                                                    apply PV_W_RecursiveLaws.bind_congr
                                                                                                    ·
                                                                                                      exact erase_invoke ops _ _
                                                                                                    · intro i25
                                                                                                      try dsimp only
                                                                                                      rw [erase_bind]
                                                                                                      apply PV_W_RecursiveLaws.bind_congr
                                                                                                      ·
                                                                                                        exact erase_invoke ops _ _
                                                                                                      · intro i26
                                                                                                        try dsimp only
                                                                                                        rw [erase_bind]
                                                                                                        apply PV_W_RecursiveLaws.bind_congr
                                                                                                        ·
                                                                                                          exact erase_invoke ops _ _
                                                                                                        · intro i27
                                                                                                          try dsimp only
                                                                                                          rw [erase_bind]
                                                                                                          apply PV_W_RecursiveLaws.bind_congr
                                                                                                          ·
                                                                                                            exact erase_invoke ops _ _
                                                                                                          · intro o6
                                                                                                            try dsimp only
                                                                                                            rw [erase_bind]
                                                                                                            apply PV_W_RecursiveLaws.bind_congr
                                                                                                            ·
                                                                                                              exact erase_invoke ops _ _
                                                                                                            · intro r6
                                                                                                              try dsimp only
                                                                                                              rw [erase_bind]
                                                                                                              apply PV_W_RecursiveLaws.bind_congr
                                                                                                              ·
                                                                                                                exact erase_invoke ops _ _
                                                                                                              · intro cf6
                                                                                                                try dsimp only
                                                                                                                cases cf6 with
                                                                                                                | Continue val6 =>
                                                                                                                  try dsimp only
                                                                                                                  rw [erase_bind]
                                                                                                                  apply PV_W_RecursiveLaws.bind_congr
                                                                                                                  ·
                                                                                                                    exact erase_invoke ops _ _
                                                                                                                  · intro i28
                                                                                                                    try dsimp only
                                                                                                                    rw [erase_bind]
                                                                                                                    apply PV_W_RecursiveLaws.bind_congr
                                                                                                                    ·
                                                                                                                      exact erase_invoke ops _ _
                                                                                                                    · intro i29
                                                                                                                      try dsimp only
                                                                                                                      rw [erase_bind]
                                                                                                                      apply PV_W_RecursiveLaws.bind_congr
                                                                                                                      ·
                                                                                                                        exact erase_invoke ops _ _
                                                                                                                      · intro i30
                                                                                                                        try dsimp only
                                                                                                                        rw [erase_bind]
                                                                                                                        apply PV_W_RecursiveLaws.bind_congr
                                                                                                                        ·
                                                                                                                          exact erase_invoke ops _ _
                                                                                                                        · intro i31
                                                                                                                          try dsimp only
                                                                                                                          rw [erase_bind]
                                                                                                                          apply PV_W_RecursiveLaws.bind_congr
                                                                                                                          ·
                                                                                                                            exact erase_invoke ops _ _
                                                                                                                          · intro o7
                                                                                                                            try dsimp only
                                                                                                                            rw [erase_bind]
                                                                                                                            apply PV_W_RecursiveLaws.bind_congr
                                                                                                                            ·
                                                                                                                              exact erase_invoke ops _ _
                                                                                                                            · intro r7
                                                                                                                              try dsimp only
                                                                                                                              rw [erase_bind]
                                                                                                                              apply PV_W_RecursiveLaws.bind_congr
                                                                                                                              ·
                                                                                                                                exact erase_invoke ops _ _
                                                                                                                              · intro cf7
                                                                                                                                try dsimp only
                                                                                                                                cases cf7 with
                                                                                                                                | Continue val7 =>
                                                                                                                                  rfl
                                                                                                                                | Break residual =>
                                                                                                                                  exact erase_invoke ops _ _
                                                                                                                | Break residual =>
                                                                                                                  exact erase_invoke ops _ _
                                                                                                | Break residual =>
                                                                                                  exact erase_invoke ops _ _
                                                                                | Break residual =>
                                                                                  exact erase_invoke ops _ _
                                                                | Break residual =>
                                                                  exact erase_invoke ops _ _
                                                | Break residual =>
                                                  exact erase_invoke ops _ _
                                | Break residual =>
                                  exact erase_invoke ops _ _
                | Break residual =>
                  exact erase_invoke ops _ _

#print axioms source
end R1Z.PV_RJDec_Parser03
