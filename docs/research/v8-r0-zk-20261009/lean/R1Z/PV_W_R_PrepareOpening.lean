import R1Z.PV_W_StructuredBinds
import R1Z.PV_W_RecursiveLaws
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_W_R_PrepareOpening
open Aeneas Aeneas.Std ProverRwFull PV_W_ReachedEffects PV_W_Callbacks
variable [ExternalTypes]

def program
  (variant : transport.Variant)
  (hash : Hash)
  (backend : prover.Backend)
  (sem : host_semantic.BuiltSemantics aspis_core.digest.LegacyHashFn) :
  P (core.result.Result prover.PreparedOpening verifier.Error) := do
  let b ← invoke "core.cmp.PartialEq.ne.trait_default" (fun ops =>
      letI : ExternalFuns := ops
      let hash := sourceHash ops hash
      core.cmp.PartialEq.ne.trait_default
      transport.Variant.Insts.CoreCmpPartialEqVariant variant
      transport.Variant.S2)
  if b then
    pure (core.result.Result.Err verifier.Error.Semantic)
  else
    let s := alloc.vec.Vec.deref backend.messages
    let coefficients ← invoke "prover.opening_coefficients" (fun ops =>
        letI : ExternalFuns := ops
        let hash := sourceHash ops hash
        prover.opening_coefficients variant s)
    let scp ← invoke "Array.index_usize" (fun ops =>
        letI : ExternalFuns := ops
        let hash := sourceHash ops hash
        Array.index_usize sem.z 1#usize)
    let we ← invoke "aspis_core.field.wide_exact.WideExact.from_qm31" (fun ops =>
        letI : ExternalFuns := ops
        let hash := sourceHash ops hash
        aspis_core.field.wide_exact.WideExact.from_qm31 scp.x)
    let we1 ← invoke "aspis_core.field.wide_exact.WideExact.from_qm31" (fun ops =>
        letI : ExternalFuns := ops
        let hash := sourceHash ops hash
        aspis_core.field.wide_exact.WideExact.from_qm31 scp.y)
    let s1 := alloc.vec.Vec.deref coefficients
    let y1 ← invoke "prover.opening_claim_bytes" (fun ops =>
        letI : ExternalFuns := ops
        let hash := sourceHash ops hash
        prover.opening_claim_bytes s1 { x := we, y := we1 })
    let a ← invoke "host_wire.SemanticTranscript.impl.state" (fun ops =>
        letI : ExternalFuns := ops
        let hash := sourceHash ops hash
        host_wire.SemanticTranscript.impl.state
        aspis_core.digest.LegacyHashFn.Insts.Aspis_coreDigestDigest32
        sem.transcript)
    let transcript ← invoke "host_transcript.Transcript.new" (fun ops =>
        letI : ExternalFuns := ops
        let hash := sourceHash ops hash
        host_transcript.Transcript.new
        aspis_core.digest.LegacyHashFn.Insts.Aspis_coreDigestDigest32 hash a
        variant)
    let s2 := alloc.vec.Vec.deref y1
    let (gamma, transcript1) ← invoke "host_transcript.Transcript.scalar" (fun ops =>
        letI : ExternalFuns := ops
        let hash := sourceHash ops hash
        host_transcript.Transcript.scalar
        aspis_core.digest.LegacyHashFn.Insts.Aspis_coreDigestDigest32
        transcript 27#u8 s2 true)
    let s3 := alloc.vec.Vec.deref coefficients
    let q ← invoke "prover.opening_batch" (fun ops =>
        letI : ExternalFuns := ops
        let hash := sourceHash ops hash
        prover.opening_batch s3 gamma)
    let r ← invoke "weights.Weights.new" (fun ops =>
        letI : ExternalFuns := ops
        let hash := sourceHash ops hash
        weights.Weights.new variant sem.alpha sem.z)
    let cf ← invoke "core.result.Result.Insts.CoreOpsTry.branch" (fun ops =>
        letI : ExternalFuns := ops
        let hash := sourceHash ops hash
        core.result.Result.Insts.CoreOpsTry.branch r)
    match cf with
    | core.ops.control_flow.ControlFlow.Continue val =>
      let s4 := alloc.vec.Vec.deref q
      let inactive ← invoke "prover.opening_inactive" (fun ops =>
          letI : ExternalFuns := ops
          let hash := sourceHash ops hash
          prover.opening_inactive s4 val)
      let a1 ← invoke "aspis_core.field.wide_exact.WideExact.to_le_bytes" (fun ops =>
          letI : ExternalFuns := ops
          let hash := sourceHash ops hash
          aspis_core.field.wide_exact.WideExact.to_le_bytes inactive)
      let s5 ← invoke "Aeneas.Std.lift" (fun ops =>
          letI : ExternalFuns := ops
          let hash := sourceHash ops hash
          Aeneas.Std.lift (Array.to_slice a1))
      let (kappa, transcript2) ← invoke "host_transcript.Transcript.scalar" (fun ops =>
          letI : ExternalFuns := ops
          let hash := sourceHash ops hash
          host_transcript.Transcript.scalar
          aspis_core.digest.LegacyHashFn.Insts.Aspis_coreDigestDigest32
          transcript1 28#u8 s5 false)
      let r1 ← invoke "weights.Weights.materialize" (fun ops =>
          letI : ExternalFuns := ops
          let hash := sourceHash ops hash
          weights.Weights.materialize val kappa)
      let cf1 ← invoke "core.result.Result.Insts.CoreOpsTry.branch" (fun ops =>
          letI : ExternalFuns := ops
          let hash := sourceHash ops hash
          core.result.Result.Insts.CoreOpsTry.branch r1)
      match cf1 with
      | core.ops.control_flow.ControlFlow.Continue val1 =>
        let s6 := alloc.vec.Vec.deref q
        let s7 := alloc.vec.Vec.deref val1
        let c0 ← invoke "prover.round" (fun ops =>
            letI : ExternalFuns := ops
            let hash := sourceHash ops hash
            prover.round s6 s7)
        let s8 ← invoke "Aeneas.Std.lift" (fun ops =>
            letI : ExternalFuns := ops
            let hash := sourceHash ops hash
            Aeneas.Std.lift (Array.to_slice c0))
        let c0bytes ← invoke "prover.encoded_slice" (fun ops =>
            letI : ExternalFuns := ops
            let hash := sourceHash ops hash
            prover.encoded_slice s8)
        let s9 := alloc.vec.Vec.deref c0bytes
        let (alpha0, transcript3) ← invoke "host_transcript.Transcript.scalar" (fun ops =>
            letI : ExternalFuns := ops
            let hash := sourceHash ops hash
            host_transcript.Transcript.scalar
            aspis_core.digest.LegacyHashFn.Insts.Aspis_coreDigestDigest32
            transcript2 29#u8 s9 false)
        let s10 := alloc.vec.Vec.deref q
        let q1 ← invoke "prover.fold" (fun ops =>
            letI : ExternalFuns := ops
            let hash := sourceHash ops hash
            prover.fold s10 alpha0 false)
        let s11 := alloc.vec.Vec.deref val1
        let w1 ← invoke "prover.fold" (fun ops =>
            letI : ExternalFuns := ops
            let hash := sourceHash ops hash
            prover.fold s11 alpha0 true)
        let s12 := alloc.vec.Vec.deref q1
        let r2 ← invoke "host_commitment.EncodingDomain.evaluate" (fun ops =>
            letI : ExternalFuns := ops
            let hash := sourceHash ops hash
            host_commitment.EncodingDomain.evaluate
            aspis_core.field.wide_exact.WideExact.Insts.Aspis_coreR0ScalarCodeField
            backend.domain s12 0#usize)
        let r3 ← invoke "core.result.Result.map_err" (fun ops =>
            letI : ExternalFuns := ops
            let hash := sourceHash ops hash
            core.result.Result.map_err
            prover.prepare_opening.closure.Insts.CoreOpsFunctionFnOnceTupleErrorError
            r2 ())
        let cf2 ← invoke "core.result.Result.Insts.CoreOpsTry.branch" (fun ops =>
            letI : ExternalFuns := ops
            let hash := sourceHash ops hash
            core.result.Result.Insts.CoreOpsTry.branch r3)
        match cf2 with
        | core.ops.control_flow.ControlFlow.Continue val2 =>
          pure (core.result.Result.Ok
            {
            backend,
            sem,
            transcript := transcript3,
            y1,
            gamma,
            inactive,
            kappa,
            alpha0,
            c0bytes,
            q1,
            w1,
            folded_word := val2
            })
        | core.ops.control_flow.ControlFlow.Break residual =>
          invoke "core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual" (fun ops =>
            letI : ExternalFuns := ops
            let hash := sourceHash ops hash
            core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
            prover.PreparedOpening (core.convert.FromSame verifier.Error)
            residual)
      | core.ops.control_flow.ControlFlow.Break residual =>
        invoke "core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual" (fun ops =>
          letI : ExternalFuns := ops
          let hash := sourceHash ops hash
          core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
          prover.PreparedOpening (core.convert.FromSame verifier.Error)
          residual)
    | core.ops.control_flow.ControlFlow.Break residual =>
      invoke "core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual" (fun ops =>
        letI : ExternalFuns := ops
        let hash := sourceHash ops hash
        core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
        prover.PreparedOpening (core.convert.FromSame verifier.Error) residual)

theorem erase_program (ops : ExternalFuns)
  (variant : transport.Variant)
  (hash : Hash)
  (backend : prover.Backend)
  (sem : host_semantic.BuiltSemantics aspis_core.digest.LegacyHashFn) :
  erase ops (program variant hash backend sem) =
    @prover.prepare_opening _ ops variant (sourceHash ops hash) backend sem := by
  unfold program prover.prepare_opening
  try dsimp only
  rw [erase_bind]
  apply PV_W_RecursiveLaws.bind_congr
  ·
    exact erase_invoke ops _ _
  · intro b
    try dsimp only
    apply PV_W_Callbacks.erase_if_congr
    ·
      rfl
    ·
      try dsimp only
      try dsimp only
      rw [erase_bind]
      apply PV_W_RecursiveLaws.bind_congr
      ·
        exact erase_invoke ops _ _
      · intro coefficients
        try dsimp only
        rw [erase_bind]
        apply PV_W_RecursiveLaws.bind_congr
        ·
          exact erase_invoke ops _ _
        · intro scp
          try dsimp only
          rw [erase_bind]
          apply PV_W_RecursiveLaws.bind_congr
          ·
            exact erase_invoke ops _ _
          · intro we
            try dsimp only
            rw [erase_bind]
            apply PV_W_RecursiveLaws.bind_congr
            ·
              exact erase_invoke ops _ _
            · intro we1
              try dsimp only
              try dsimp only
              rw [erase_bind]
              apply PV_W_RecursiveLaws.bind_congr
              ·
                exact erase_invoke ops _ _
              · intro y1
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
                  · intro transcript
                    try dsimp only
                    try dsimp only
                    rw [erase_bind]
                    apply PV_W_RecursiveLaws.bind_congr
                    ·
                      exact erase_invoke ops _ _
                    · rintro ⟨gamma, transcript1⟩
                      try dsimp only
                      try dsimp only
                      rw [erase_bind]
                      apply PV_W_RecursiveLaws.bind_congr
                      ·
                        exact erase_invoke ops _ _
                      · intro q
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
                              try dsimp only
                              rw [erase_bind]
                              apply PV_W_RecursiveLaws.bind_congr
                              ·
                                exact erase_invoke ops _ _
                              · intro inactive
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
                                  · intro s5
                                    try dsimp only
                                    rw [erase_bind]
                                    apply PV_W_RecursiveLaws.bind_congr
                                    ·
                                      exact erase_invoke ops _ _
                                    · rintro ⟨kappa, transcript2⟩
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
                                            try dsimp only
                                            try dsimp only
                                            rw [erase_bind]
                                            apply PV_W_RecursiveLaws.bind_congr
                                            ·
                                              exact erase_invoke ops _ _
                                            · intro c0
                                              try dsimp only
                                              rw [erase_bind]
                                              apply PV_W_RecursiveLaws.bind_congr
                                              ·
                                                exact erase_invoke ops _ _
                                              · intro s8
                                                try dsimp only
                                                rw [erase_bind]
                                                apply PV_W_RecursiveLaws.bind_congr
                                                ·
                                                  exact erase_invoke ops _ _
                                                · intro c0bytes
                                                  try dsimp only
                                                  try dsimp only
                                                  rw [erase_bind]
                                                  apply PV_W_RecursiveLaws.bind_congr
                                                  ·
                                                    exact erase_invoke ops _ _
                                                  · rintro ⟨alpha0, transcript3⟩
                                                    try dsimp only
                                                    try dsimp only
                                                    rw [erase_bind]
                                                    apply PV_W_RecursiveLaws.bind_congr
                                                    ·
                                                      exact erase_invoke ops _ _
                                                    · intro q1
                                                      try dsimp only
                                                      try dsimp only
                                                      rw [erase_bind]
                                                      apply PV_W_RecursiveLaws.bind_congr
                                                      ·
                                                        exact erase_invoke ops _ _
                                                      · intro w1
                                                        try dsimp only
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
                                                          · intro r3
                                                            try dsimp only
                                                            rw [erase_bind]
                                                            apply PV_W_RecursiveLaws.bind_congr
                                                            ·
                                                              exact erase_invoke ops _ _
                                                            · intro cf2
                                                              try dsimp only
                                                              cases cf2 with
                                                              | Continue val2 =>
                                                                rfl
                                                              | Break residual =>
                                                                exact erase_invoke ops _ _
                                          | Break residual =>
                                            exact erase_invoke ops _ _
                            | Break residual =>
                              exact erase_invoke ops _ _

#print axioms erase_program
end R1Z.PV_W_R_PrepareOpening
