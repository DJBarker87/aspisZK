import R1Z.PV_W_StructuredBinds
import R1Z.PV_W_RecursiveLaws
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_W_R_FinishOpening
open Aeneas Aeneas.Std ProverRwFull PV_W_ReachedEffects PV_W_Callbacks
variable [ExternalTypes]

def program
  (variant : transport.Variant)
  (hash : Hash)
  (prepared : prover.PreparedOpening)
  (folded_salts : host_commitment.PrivateSalts) :
  P (core.result.Result prover.Publication verifier.Error) := do
  let s := alloc.vec.Vec.deref prepared.folded_word
  let leaves ← invoke "prover.folded_leaves" (fun ops =>
      letI : ExternalFuns := ops
      let hash := sourceHash ops hash
      prover.folded_leaves hash s folded_salts)
  let o ← invoke "host_tree.BinaryTree.new" (fun ops =>
      letI : ExternalFuns := ops
      let hash := sourceHash ops hash
      host_tree.BinaryTree.new
      aspis_core.digest.LegacyHashFn.Insts.Aspis_coreDigestDigest32 hash leaves)
  let r ← invoke "core.option.Option.ok_or" (fun ops =>
      letI : ExternalFuns := ops
      let hash := sourceHash ops hash
      core.option.Option.ok_or o verifier.Error.Allocation)
  let cf ← invoke "core.result.Result.Insts.CoreOpsTry.branch" (fun ops =>
      letI : ExternalFuns := ops
      let hash := sourceHash ops hash
      core.result.Result.Insts.CoreOpsTry.branch r)
  match cf with
  | core.ops.control_flow.ControlFlow.Continue val =>
    let root ← invoke "host_tree.BinaryTree.root" (fun ops =>
        letI : ExternalFuns := ops
        let hash := sourceHash ops hash
        host_tree.BinaryTree.root val)
    let s1 := alloc.vec.Vec.deref prepared.q1
    let s2 := alloc.vec.Vec.deref prepared.w1
    let c1 ← invoke "prover.round" (fun ops =>
        letI : ExternalFuns := ops
        let hash := sourceHash ops hash
        prover.round s1 s2)
    let s3 ← invoke "Aeneas.Std.lift" (fun ops =>
        letI : ExternalFuns := ops
        let hash := sourceHash ops hash
        Aeneas.Std.lift (Array.to_slice c1))
    let c1bytes ← invoke "prover.encoded_slice" (fun ops =>
        letI : ExternalFuns := ops
        let hash := sourceHash ops hash
        prover.encoded_slice s3)
    let s4 ← invoke "Aeneas.Std.lift" (fun ops =>
        letI : ExternalFuns := ops
        let hash := sourceHash ops hash
        Aeneas.Std.lift (Array.to_slice root))
    let payload ← invoke "alloc.slice.Slice.to_vec" (fun ops =>
        letI : ExternalFuns := ops
        let hash := sourceHash ops hash
        alloc.slice.Slice.to_vec core.clone.CloneU8 s4)
    let s5 := alloc.vec.Vec.deref c1bytes
    let payload1 ← invoke "alloc.vec.Vec.extend_from_slice" (fun ops =>
        letI : ExternalFuns := ops
        let hash := sourceHash ops hash
        alloc.vec.Vec.extend_from_slice core.clone.CloneU8 payload s5)
    let s6 := alloc.vec.Vec.deref payload1
    let (alpha1, transcript) ← invoke "host_transcript.Transcript.scalar" (fun ops =>
        letI : ExternalFuns := ops
        let hash := sourceHash ops hash
        host_transcript.Transcript.scalar
        aspis_core.digest.LegacyHashFn.Insts.Aspis_coreDigestDigest32
        prepared.transcript 30#u8 s6 false)
    let s7 := alloc.vec.Vec.deref prepared.q1
    let final_message ← invoke "prover.fold" (fun ops =>
        letI : ExternalFuns := ops
        let hash := sourceHash ops hash
        prover.fold s7 alpha1 false)
    let s8 := alloc.vec.Vec.deref final_message
    let fbytes ← invoke "prover.encoded_slice" (fun ops =>
        letI : ExternalFuns := ops
        let hash := sourceHash ops hash
        prover.encoded_slice s8)
    let s9 := alloc.vec.Vec.deref fbytes
    let (r1, transcript1) ← invoke "host_transcript.Transcript.queries" (fun ops =>
        letI : ExternalFuns := ops
        let hash := sourceHash ops hash
        host_transcript.Transcript.queries
        aspis_core.digest.LegacyHashFn.Insts.Aspis_coreDigestDigest32
        transcript 31#u8 s9)
    let cf1 ← invoke "core.result.Result.Insts.CoreOpsTry.branch" (fun ops =>
        letI : ExternalFuns := ops
        let hash := sourceHash ops hash
        core.result.Result.Insts.CoreOpsTry.branch r1)
    match cf1 with
    | core.ops.control_flow.ControlFlow.Continue val1 =>
      let s10 ← invoke "Aeneas.Std.lift" (fun ops =>
          letI : ExternalFuns := ops
          let hash := sourceHash ops hash
          Aeneas.Std.lift (Array.to_slice (Std.Array.empty Std.U8)))
      let _ ← invoke "host_transcript.Transcript.scalar_k" (fun ops =>
          letI : ExternalFuns := ops
          let hash := sourceHash ops hash
          host_transcript.Transcript.scalar_k
          aspis_core.digest.LegacyHashFn.Insts.Aspis_coreDigestDigest32
          transcript1 32#u8 s10)
      let scp ← invoke "Array.index_usize" (fun ops =>
          letI : ExternalFuns := ops
          let hash := sourceHash ops hash
          Array.index_usize prepared.sem.z 0#usize)
      let scp1 ← invoke "Array.index_usize" (fun ops =>
          letI : ExternalFuns := ops
          let hash := sourceHash ops hash
          Array.index_usize prepared.sem.z 1#usize)
      let s11 ← invoke "Aeneas.Std.lift" (fun ops =>
          letI : ExternalFuns := ops
          let hash := sourceHash ops hash
          Aeneas.Std.lift (Array.to_slice val1))
      let v ← invoke "alloc.slice.Slice.to_vec" (fun ops =>
          letI : ExternalFuns := ops
          let hash := sourceHash ops hash
          alloc.slice.Slice.to_vec core.clone.CloneU32 s11)
      let a ← invoke "Array.index_usize" (fun ops =>
          letI : ExternalFuns := ops
          let hash := sourceHash ops hash
          Array.index_usize prepared.sem.roots 0#usize)
      let r2 ← invoke "prover.public_check" (fun ops =>
          letI : ExternalFuns := ops
          let hash := sourceHash ops hash
          prover.public_check variant
          {
          alpha := prepared.sem.alpha,
          z :=
          (Array.make 2#usize [
          Array.make 2#usize [ scp.x, scp.y ],
          Array.make 2#usize [ scp1.x, scp1.y ]
          ]),
          gamma := prepared.gamma,
          kappa := prepared.kappa,
          alpha0 := prepared.alpha0,
          alpha1,
          queries := v
          } a)
      let cf2 ← invoke "core.result.Result.Insts.CoreOpsTry.branch" (fun ops =>
          letI : ExternalFuns := ops
          let hash := sourceHash ops hash
          core.result.Result.Insts.CoreOpsTry.branch r2)
      match cf2 with
      | core.ops.control_flow.ControlFlow.Continue _ =>
        pure (core.result.Result.Ok
          {
          backend := prepared.backend,
          semantic_bytes := prepared.sem.bytes,
          y1 := prepared.y1,
          inactive := prepared.inactive,
          c0bytes := prepared.c0bytes,
          root,
          c1bytes,
          fbytes,
          queries := val1,
          folded_word := prepared.folded_word,
          folded_salts,
          tree := val
          })
      | core.ops.control_flow.ControlFlow.Break residual =>
        invoke "core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual" (fun ops =>
          letI : ExternalFuns := ops
          let hash := sourceHash ops hash
          core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
          prover.Publication (core.convert.FromSame verifier.Error) residual)
    | core.ops.control_flow.ControlFlow.Break residual =>
      invoke "core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual" (fun ops =>
        letI : ExternalFuns := ops
        let hash := sourceHash ops hash
        core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
        prover.Publication (core.convert.FromSame verifier.Error) residual)
  | core.ops.control_flow.ControlFlow.Break residual =>
    invoke "core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual" (fun ops =>
      letI : ExternalFuns := ops
      let hash := sourceHash ops hash
      core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
      prover.Publication (core.convert.FromSame verifier.Error) residual)

theorem erase_program (ops : ExternalFuns)
  (variant : transport.Variant)
  (hash : Hash)
  (prepared : prover.PreparedOpening)
  (folded_salts : host_commitment.PrivateSalts) :
  erase ops (program variant hash prepared folded_salts) =
    @prover.finish_opening _ ops variant (sourceHash ops hash) prepared folded_salts := by
  unfold program prover.finish_opening
  try dsimp only
  try dsimp only
  rw [erase_bind]
  apply PV_W_RecursiveLaws.bind_congr
  ·
    exact erase_invoke ops _ _
  · intro leaves
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
            · intro root
              try dsimp only
              try dsimp only
              try dsimp only
              rw [erase_bind]
              apply PV_W_RecursiveLaws.bind_congr
              ·
                exact erase_invoke ops _ _
              · intro c1
                try dsimp only
                rw [erase_bind]
                apply PV_W_RecursiveLaws.bind_congr
                ·
                  exact erase_invoke ops _ _
                · intro s3
                  try dsimp only
                  rw [erase_bind]
                  apply PV_W_RecursiveLaws.bind_congr
                  ·
                    exact erase_invoke ops _ _
                  · intro c1bytes
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
                      · intro payload
                        try dsimp only
                        try dsimp only
                        rw [erase_bind]
                        apply PV_W_RecursiveLaws.bind_congr
                        ·
                          exact erase_invoke ops _ _
                        · intro payload1
                          try dsimp only
                          try dsimp only
                          rw [erase_bind]
                          apply PV_W_RecursiveLaws.bind_congr
                          ·
                            exact erase_invoke ops _ _
                          · rintro ⟨alpha1, transcript⟩
                            try dsimp only
                            try dsimp only
                            rw [erase_bind]
                            apply PV_W_RecursiveLaws.bind_congr
                            ·
                              exact erase_invoke ops _ _
                            · intro final_message
                              try dsimp only
                              try dsimp only
                              rw [erase_bind]
                              apply PV_W_RecursiveLaws.bind_congr
                              ·
                                exact erase_invoke ops _ _
                              · intro fbytes
                                try dsimp only
                                try dsimp only
                                rw [erase_bind]
                                apply PV_W_RecursiveLaws.bind_congr
                                ·
                                  exact erase_invoke ops _ _
                                · rintro ⟨r1, transcript1⟩
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
                                      · intro s10
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
                                          · intro scp
                                            try dsimp only
                                            rw [erase_bind]
                                            apply PV_W_RecursiveLaws.bind_congr
                                            ·
                                              exact erase_invoke ops _ _
                                            · intro scp1
                                              try dsimp only
                                              rw [erase_bind]
                                              apply PV_W_RecursiveLaws.bind_congr
                                              ·
                                                exact erase_invoke ops _ _
                                              · intro s11
                                                try dsimp only
                                                rw [erase_bind]
                                                apply PV_W_RecursiveLaws.bind_congr
                                                ·
                                                  exact erase_invoke ops _ _
                                                · intro v
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
                                                    · intro r2
                                                      try dsimp only
                                                      rw [erase_bind]
                                                      apply PV_W_RecursiveLaws.bind_congr
                                                      ·
                                                        exact erase_invoke ops _ _
                                                      · intro cf2
                                                        try dsimp only
                                                        cases cf2 with
                                                        | Continue unused0_0 =>
                                                          rfl
                                                        | Break residual =>
                                                          exact erase_invoke ops _ _
                                    | Break residual =>
                                      exact erase_invoke ops _ _
          | Break residual =>
            exact erase_invoke ops _ _

#print axioms erase_program
end R1Z.PV_W_R_FinishOpening
