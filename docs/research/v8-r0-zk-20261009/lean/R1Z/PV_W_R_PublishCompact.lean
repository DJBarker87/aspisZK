import R1Z.PV_W_StructuredBinds
import R1Z.PV_W_RecursiveLaws
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_W_R_PublishCompact
open Aeneas Aeneas.Std ProverRwFull PV_W_ReachedEffects PV_W_Callbacks
variable [ExternalTypes]

def program
  (variant : transport.Variant) (p : prover.Publication) :
  P (core.result.Result (alloc.vec.Vec Std.U8) verifier.Error) := do
  let i ← invoke "compact.PROOF_BYTES" (fun ops =>
      letI : ExternalFuns := ops
      compact.PROOF_BYTES)
  let out := alloc.vec.Vec.with_capacity Std.U8 i
  let a ← invoke "compact.MAGIC" (fun ops =>
      letI : ExternalFuns := ops
      compact.MAGIC)
  let s ← invoke "Aeneas.Std.lift" (fun ops =>
      letI : ExternalFuns := ops
      Aeneas.Std.lift (Array.to_slice a))
  let out1 ← invoke "alloc.vec.Vec.extend_from_slice" (fun ops =>
      letI : ExternalFuns := ops
      alloc.vec.Vec.extend_from_slice core.clone.CloneU8 out s)
  let i1 ← invoke "transport.Variant.tag" (fun ops =>
      letI : ExternalFuns := ops
      transport.Variant.tag variant)
  let s1 ← invoke "Aeneas.Std.lift" (fun ops =>
      letI : ExternalFuns := ops
      Aeneas.Std.lift (Array.to_slice
      (Array.make 8#usize [ i1, 0#u8, 0#u8, 0#u8, 0#u8, 0#u8, 0#u8, 0#u8 ])))
  let out2 ← invoke "alloc.vec.Vec.extend_from_slice" (fun ops =>
      letI : ExternalFuns := ops
      alloc.vec.Vec.extend_from_slice core.clone.CloneU8 out1 s1)
  let s2 := alloc.vec.Vec.deref p.semantic_bytes
  let (r, out3) ← invoke "host_compact.compact_semantic" (fun ops =>
      letI : ExternalFuns := ops
      host_compact.compact_semantic s2 out2)
  let r1 ← invoke "core.result.Result.map_err" (fun ops =>
      letI : ExternalFuns := ops
      core.result.Result.map_err
      prover.publish_compact.closure.Insts.CoreOpsFunctionFnOnceTupleCodecErrorError
      r ())
  let cf ← invoke "core.result.Result.Insts.CoreOpsTry.branch" (fun ops =>
      letI : ExternalFuns := ops
      core.result.Result.Insts.CoreOpsTry.branch r1)
  match cf with
  | core.ops.control_flow.ControlFlow.Continue _ =>
    let s3 := alloc.vec.Vec.deref p.y1
    let (r2, out4) ← invoke "host_compact.compact_values" (fun ops =>
        letI : ExternalFuns := ops
        host_compact.compact_values s3 out3)
    let r3 ← invoke "core.result.Result.map_err" (fun ops =>
        letI : ExternalFuns := ops
        core.result.Result.map_err
        prover.publish_compact.closure_1.Insts.CoreOpsFunctionFnOnceTupleCodecErrorError
        r2 ())
    let cf1 ← invoke "core.result.Result.Insts.CoreOpsTry.branch" (fun ops =>
        letI : ExternalFuns := ops
        core.result.Result.Insts.CoreOpsTry.branch r3)
    match cf1 with
    | core.ops.control_flow.ControlFlow.Continue _ =>
      let a1 ← invoke "aspis_core.field.wide_exact.WideExact.to_le_bytes" (fun ops =>
          letI : ExternalFuns := ops
          aspis_core.field.wide_exact.WideExact.to_le_bytes p.inactive)
      let s4 ← invoke "Aeneas.Std.lift" (fun ops =>
          letI : ExternalFuns := ops
          Aeneas.Std.lift (Array.to_slice a1))
      let out5 ← invoke "alloc.vec.Vec.extend_from_slice" (fun ops =>
          letI : ExternalFuns := ops
          alloc.vec.Vec.extend_from_slice core.clone.CloneU8 out4 s4)
      let s5 := alloc.vec.Vec.deref p.c0bytes
      let out6 ← invoke "alloc.vec.Vec.extend_from_slice" (fun ops =>
          letI : ExternalFuns := ops
          alloc.vec.Vec.extend_from_slice core.clone.CloneU8 out5 s5)
      let s6 ← invoke "Aeneas.Std.lift" (fun ops =>
          letI : ExternalFuns := ops
          Aeneas.Std.lift (Array.to_slice p.root))
      let out7 ← invoke "alloc.vec.Vec.extend_from_slice" (fun ops =>
          letI : ExternalFuns := ops
          alloc.vec.Vec.extend_from_slice core.clone.CloneU8 out6 s6)
      let s7 := alloc.vec.Vec.deref p.c1bytes
      let out8 ← invoke "alloc.vec.Vec.extend_from_slice" (fun ops =>
          letI : ExternalFuns := ops
          alloc.vec.Vec.extend_from_slice core.clone.CloneU8 out7 s7)
      let s8 := alloc.vec.Vec.deref p.fbytes
      let out9 ← invoke "alloc.vec.Vec.extend_from_slice" (fun ops =>
          letI : ExternalFuns := ops
          alloc.vec.Vec.extend_from_slice core.clone.CloneU8 out8 s8)
      let left_val := alloc.vec.Vec.len out9
      let right_val ← invoke "compact.OFF_OPENINGS" (fun ops =>
          letI : ExternalFuns := ops
          compact.OFF_OPENINGS)
      let _ ← invoke "massert" (fun ops =>
          letI : ExternalFuns := ops
          massert (left_val = right_val))
      let (o, _) := core.option.Option.take p.backend.c1
      let cc1 ← invoke "core.option.Option.unwrap" (fun ops =>
          letI : ExternalFuns := ops
          core.option.Option.unwrap o)
      let (o1, _) := core.option.Option.take p.backend.c2
      let cc2 ← invoke "core.option.Option.unwrap" (fun ops =>
          letI : ExternalFuns := ops
          core.option.Option.unwrap o1)
      let s9 := alloc.vec.Vec.deref p.folded_word
      let out10 ← invoke "prover.append_query_openings" (fun ops =>
          letI : ExternalFuns := ops
          prover.append_query_openings out9 cc1 cc2 p.queries s9 p.folded_salts)
      let left_val1 := alloc.vec.Vec.len out10
      let right_val1 ← invoke "compact.OFF_NODES" (fun ops =>
          letI : ExternalFuns := ops
          compact.OFF_NODES)
      let _ ← invoke "massert" (fun ops =>
          letI : ExternalFuns := ops
          massert (left_val1 = right_val1))
      let r4 ← invoke "prover.append_node_slots" (fun ops =>
          letI : ExternalFuns := ops
          prover.append_node_slots out10 cc1 cc2 p.tree p.queries)
      let cf2 ← invoke "core.result.Result.Insts.CoreOpsTry.branch" (fun ops =>
          letI : ExternalFuns := ops
          core.result.Result.Insts.CoreOpsTry.branch r4)
      match cf2 with
      | core.ops.control_flow.ControlFlow.Continue val =>
        let left_val2 := alloc.vec.Vec.len val
        let _ ← invoke "massert" (fun ops =>
            letI : ExternalFuns := ops
            massert (left_val2 = i))
        pure (core.result.Result.Ok val)
      | core.ops.control_flow.ControlFlow.Break residual =>
        invoke "core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual" (fun ops =>
          letI : ExternalFuns := ops
          core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
          (alloc.vec.Vec Std.U8) (core.convert.FromSame verifier.Error)
          residual)
    | core.ops.control_flow.ControlFlow.Break residual =>
      invoke "core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual" (fun ops =>
        letI : ExternalFuns := ops
        core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
        (alloc.vec.Vec Std.U8) (core.convert.FromSame verifier.Error) residual)
  | core.ops.control_flow.ControlFlow.Break residual =>
    invoke "core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual" (fun ops =>
      letI : ExternalFuns := ops
      core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
      (alloc.vec.Vec Std.U8) (core.convert.FromSame verifier.Error) residual)

theorem erase_program (ops : ExternalFuns)
  (variant : transport.Variant) (p : prover.Publication) :
  erase ops (program variant p) =
    @prover.publish_compact _ ops variant p := by
  unfold program prover.publish_compact
  try dsimp only
  rw [erase_bind]
  apply PV_W_RecursiveLaws.bind_congr
  ·
    exact erase_invoke ops _ _
  · intro i
    try dsimp only
    try dsimp only
    rw [erase_bind]
    apply PV_W_RecursiveLaws.bind_congr
    ·
      exact erase_invoke ops _ _
    · intro a
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
          exact erase_invoke ops _ _
        · intro out1
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
            · intro s1
              try dsimp only
              rw [erase_bind]
              apply PV_W_RecursiveLaws.bind_congr
              ·
                exact erase_invoke ops _ _
              · intro out2
                try dsimp only
                try dsimp only
                rw [erase_bind]
                apply PV_W_RecursiveLaws.bind_congr
                ·
                  exact erase_invoke ops _ _
                · rintro ⟨r, out3⟩
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
                    · intro cf
                      try dsimp only
                      cases cf with
                      | Continue unused0_0 =>
                        try dsimp only
                        try dsimp only
                        rw [erase_bind]
                        apply PV_W_RecursiveLaws.bind_congr
                        ·
                          exact erase_invoke ops _ _
                        · rintro ⟨r2, out4⟩
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
                            · intro cf1
                              try dsimp only
                              cases cf1 with
                              | Continue unused0_0 =>
                                try dsimp only
                                rw [erase_bind]
                                apply PV_W_RecursiveLaws.bind_congr
                                ·
                                  exact erase_invoke ops _ _
                                · intro a1
                                  try dsimp only
                                  rw [erase_bind]
                                  apply PV_W_RecursiveLaws.bind_congr
                                  ·
                                    exact erase_invoke ops _ _
                                  · intro s4
                                    try dsimp only
                                    rw [erase_bind]
                                    apply PV_W_RecursiveLaws.bind_congr
                                    ·
                                      exact erase_invoke ops _ _
                                    · intro out5
                                      try dsimp only
                                      try dsimp only
                                      rw [erase_bind]
                                      apply PV_W_RecursiveLaws.bind_congr
                                      ·
                                        exact erase_invoke ops _ _
                                      · intro out6
                                        try dsimp only
                                        rw [erase_bind]
                                        apply PV_W_RecursiveLaws.bind_congr
                                        ·
                                          exact erase_invoke ops _ _
                                        · intro s6
                                          try dsimp only
                                          rw [erase_bind]
                                          apply PV_W_RecursiveLaws.bind_congr
                                          ·
                                            exact erase_invoke ops _ _
                                          · intro out7
                                            try dsimp only
                                            try dsimp only
                                            rw [erase_bind]
                                            apply PV_W_RecursiveLaws.bind_congr
                                            ·
                                              exact erase_invoke ops _ _
                                            · intro out8
                                              try dsimp only
                                              try dsimp only
                                              rw [erase_bind]
                                              apply PV_W_RecursiveLaws.bind_congr
                                              ·
                                                exact erase_invoke ops _ _
                                              · intro out9
                                                try dsimp only
                                                try dsimp only
                                                rw [erase_bind]
                                                apply PV_W_RecursiveLaws.bind_congr
                                                ·
                                                  exact erase_invoke ops _ _
                                                · intro right_val
                                                  try dsimp only
                                                  rw [erase_bind]
                                                  apply PV_W_RecursiveLaws.bind_congr
                                                  ·
                                                    exact erase_invoke ops _ _
                                                  · intro _
                                                    try dsimp only
                                                    try dsimp only
                                                    rw [erase_bind]
                                                    apply PV_W_RecursiveLaws.bind_congr
                                                    ·
                                                      exact erase_invoke ops _ _
                                                    · intro cc1
                                                      try dsimp only
                                                      try dsimp only
                                                      rw [erase_bind]
                                                      apply PV_W_RecursiveLaws.bind_congr
                                                      ·
                                                        exact erase_invoke ops _ _
                                                      · intro cc2
                                                        try dsimp only
                                                        try dsimp only
                                                        rw [erase_bind]
                                                        apply PV_W_RecursiveLaws.bind_congr
                                                        ·
                                                          exact erase_invoke ops _ _
                                                        · intro out10
                                                          try dsimp only
                                                          try dsimp only
                                                          rw [erase_bind]
                                                          apply PV_W_RecursiveLaws.bind_congr
                                                          ·
                                                            exact erase_invoke ops _ _
                                                          · intro right_val1
                                                            try dsimp only
                                                            rw [erase_bind]
                                                            apply PV_W_RecursiveLaws.bind_congr
                                                            ·
                                                              exact erase_invoke ops _ _
                                                            · intro _
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
                                                                · intro cf2
                                                                  try dsimp only
                                                                  cases cf2 with
                                                                  | Continue val =>
                                                                    try dsimp only
                                                                    try dsimp only
                                                                    rw [erase_bind]
                                                                    apply PV_W_RecursiveLaws.bind_congr
                                                                    ·
                                                                      exact erase_invoke ops _ _
                                                                    · intro _
                                                                      rfl
                                                                  | Break residual =>
                                                                    exact erase_invoke ops _ _
                              | Break residual =>
                                exact erase_invoke ops _ _
                      | Break residual =>
                        exact erase_invoke ops _ _

#print axioms erase_program
end R1Z.PV_W_R_PublishCompact
