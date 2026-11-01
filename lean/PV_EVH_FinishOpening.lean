import PV_EVH_Prefix
set_option autoImplicit false
noncomputable section
namespace PV_EVH_FinishOpening
open Aeneas Aeneas.Std ProverRwFull PV_EVH_World
open PV_EVH_Prefix (P FinishedView)
variable [ExternalTypes] [ExternalFuns]

/-- Every non-language callee is explicitly OPEN. This structure supplies
neither a complete native event trace nor any successful run witness. -/
structure Callees where
  folded_leaves_OPEN : ∀ (hash : Slice (Slice Std.U8) → Result (Array Std.U8 32#usize))
  (word : Slice aspis_core.field.wide_exact.WideExact)
  (salts : host_commitment.PrivateSalts), P ((alloc.vec.Vec (Array Std.U8 32#usize)))
  new_OPEN : ∀ {H : Type} (aspis_coredigestDigest32Inst : aspis_core.digest.Digest32 H)
  (hash : H) (leaves : alloc.vec.Vec (Array Std.U8 32#usize)), P ((Option host_tree.BinaryTree))
  op7_OPEN : ∀ {T : Type} {E : Type} (arg0 : (Option T)) (arg1 : E), P ((core.result.Result T E))
  root_OPEN : ∀ (self : host_tree.BinaryTree), P ((Array Std.U8 32#usize))
  round_OPEN : ∀ (q : Slice aspis_core.field.wide_exact.WideExact)
  (w : Slice aspis_core.field.wide_exact.WideExact), P ((Array aspis_core.field.wide_exact.WideExact 7#usize))
  encoded_slice_OPEN : ∀ (values : Slice aspis_core.field.wide_exact.WideExact), P ((alloc.vec.Vec Std.U8))
  toVec_OPEN : ∀ {T : Type} (inst : core.clone.Clone T) (s : Slice T), P (alloc.vec.Vec T)
  extendFromSlice_OPEN : ∀ {T : Type} (inst : core.clone.Clone T) (v : alloc.vec.Vec T) (s : Slice T), P (alloc.vec.Vec T)
  scalar_OPEN : ∀ {H : Type} (aspis_coredigestDigest32Inst : aspis_core.digest.Digest32 H)
  (self : host_transcript.Transcript H) (row : Std.U8) (payload : Slice Std.U8)
  (nonzero : Bool), P ((aspis_core.field.wide_exact.WideExact × (host_transcript.Transcript
    H)))
  fold_OPEN : ∀ (q : Slice aspis_core.field.wide_exact.WideExact)
  (alpha : aspis_core.field.wide_exact.WideExact) (dual : Bool), P ((alloc.vec.Vec aspis_core.field.wide_exact.WideExact))
  queries_OPEN : ∀ {H : Type} (aspis_coredigestDigest32Inst : aspis_core.digest.Digest32 H)
  (self : host_transcript.Transcript H) (row : Std.U8) (payload : Slice Std.U8), P (((core.result.Result (Array Std.U32 22#usize) verifier.Error) ×
    (host_transcript.Transcript H)))
  scalar_k_OPEN : ∀ {H : Type} (aspis_coredigestDigest32Inst : aspis_core.digest.Digest32 H)
  (self : host_transcript.Transcript H) (row : Std.U8) (payload : Slice Std.U8), P ((aspis_core.field.QM31 × (host_transcript.Transcript H)))
  public_check_OPEN : ∀ (variant : transport.Variant)
  (challenges : aspis_z4b_probe.probe.z9.z9b.z9c.z9d.z9e.R1PublicChallenges)
  (c1_root : Array Std.U8 32#usize), P ((core.result.Result Unit verifier.Error))

structure Compatible (c : Callees) : Prop where
  folded_leaves_fixed : ∀ (hash : Slice (Slice Std.U8) → Result (Array Std.U8 32#usize))
  (word : Slice aspis_core.field.wide_exact.WideExact)
  (salts : host_commitment.PrivateSalts), FinishedView (c.folded_leaves_OPEN hash word salts) (prover.folded_leaves hash word salts)
  new_fixed : ∀ {H : Type} (aspis_coredigestDigest32Inst : aspis_core.digest.Digest32 H)
  (hash : H) (leaves : alloc.vec.Vec (Array Std.U8 32#usize)), FinishedView (c.new_OPEN aspis_coredigestDigest32Inst hash leaves) (host_tree.BinaryTree.new aspis_coredigestDigest32Inst hash leaves)
  op7_fixed : ∀ {T : Type} {E : Type} (arg0 : (Option T)) (arg1 : E), FinishedView (c.op7_OPEN arg0 arg1) (core.option.Option.ok_or arg0 arg1)
  root_fixed : ∀ (self : host_tree.BinaryTree), FinishedView (c.root_OPEN self) (host_tree.BinaryTree.root self)
  round_fixed : ∀ (q : Slice aspis_core.field.wide_exact.WideExact)
  (w : Slice aspis_core.field.wide_exact.WideExact), FinishedView (c.round_OPEN q w) (prover.round q w)
  encoded_slice_fixed : ∀ (values : Slice aspis_core.field.wide_exact.WideExact), FinishedView (c.encoded_slice_OPEN values) (prover.encoded_slice values)
  toVec_fixed : ∀ {T : Type} (inst : core.clone.Clone T) (s : Slice T), FinishedView (c.toVec_OPEN inst s) (alloc.slice.Slice.to_vec inst s)
  extendFromSlice_fixed : ∀ {T : Type} (inst : core.clone.Clone T) (v : alloc.vec.Vec T) (s : Slice T), FinishedView (c.extendFromSlice_OPEN inst v s) (alloc.vec.Vec.extend_from_slice inst v s)
  scalar_fixed : ∀ {H : Type} (aspis_coredigestDigest32Inst : aspis_core.digest.Digest32 H)
  (self : host_transcript.Transcript H) (row : Std.U8) (payload : Slice Std.U8)
  (nonzero : Bool), FinishedView (c.scalar_OPEN aspis_coredigestDigest32Inst self row payload nonzero) (host_transcript.Transcript.scalar aspis_coredigestDigest32Inst self row payload nonzero)
  fold_fixed : ∀ (q : Slice aspis_core.field.wide_exact.WideExact)
  (alpha : aspis_core.field.wide_exact.WideExact) (dual : Bool), FinishedView (c.fold_OPEN q alpha dual) (prover.fold q alpha dual)
  queries_fixed : ∀ {H : Type} (aspis_coredigestDigest32Inst : aspis_core.digest.Digest32 H)
  (self : host_transcript.Transcript H) (row : Std.U8) (payload : Slice Std.U8), FinishedView (c.queries_OPEN aspis_coredigestDigest32Inst self row payload) (host_transcript.Transcript.queries aspis_coredigestDigest32Inst self row payload)
  scalar_k_fixed : ∀ {H : Type} (aspis_coredigestDigest32Inst : aspis_core.digest.Digest32 H)
  (self : host_transcript.Transcript H) (row : Std.U8) (payload : Slice Std.U8), FinishedView (c.scalar_k_OPEN aspis_coredigestDigest32Inst self row payload) (host_transcript.Transcript.scalar_k aspis_coredigestDigest32Inst self row payload)
  public_check_fixed : ∀ (variant : transport.Variant)
  (challenges : aspis_z4b_probe.probe.z9.z9b.z9c.z9d.z9e.R1PublicChallenges)
  (c1_root : Array Std.U8 32#usize), FinishedView (c.public_check_OPEN variant challenges c1_root) (prover.public_check variant challenges c1_root)

def run
  (variant : transport.Variant)
  (hash : Slice (Slice Std.U8) → Result (Array Std.U8 32#usize))
  (prepared : prover.PreparedOpening)
  (folded_salts : host_commitment.PrivateSalts) (c : Callees) : P (core.result.Result prover.Publication verifier.Error) := do
  let s := alloc.vec.Vec.deref prepared.folded_word
  let leaves ← c.folded_leaves_OPEN hash s folded_salts
  let o ← c.new_OPEN
      aspis_core.digest.LegacyHashFn.Insts.Aspis_coreDigestDigest32 hash leaves
  let r ← c.op7_OPEN o verifier.Error.Allocation
  let cf ← PV_EVH_Prefix.lift (core.result.Result.Insts.CoreOpsTry.branch r)
  match cf with
  | core.ops.control_flow.ControlFlow.Continue val =>
    let root ← c.root_OPEN val
    let s1 := alloc.vec.Vec.deref prepared.q1
    let s2 := alloc.vec.Vec.deref prepared.w1
    let c1 ← c.round_OPEN s1 s2
    let s3 ← PV_EVH_Prefix.lift (Aeneas.Std.lift (Array.to_slice c1))
    let c1bytes ← c.encoded_slice_OPEN s3
    let s4 ← PV_EVH_Prefix.lift (Aeneas.Std.lift (Array.to_slice root))
    let payload ← c.toVec_OPEN core.clone.CloneU8 s4
    let s5 := alloc.vec.Vec.deref c1bytes
    let payload1 ← c.extendFromSlice_OPEN core.clone.CloneU8 payload s5
    let s6 := alloc.vec.Vec.deref payload1
    let (alpha1, transcript) ← c.scalar_OPEN
        aspis_core.digest.LegacyHashFn.Insts.Aspis_coreDigestDigest32
        prepared.transcript 30#u8 s6 false
    let s7 := alloc.vec.Vec.deref prepared.q1
    let final_message ← c.fold_OPEN s7 alpha1 false
    let s8 := alloc.vec.Vec.deref final_message
    let fbytes ← c.encoded_slice_OPEN s8
    let s9 := alloc.vec.Vec.deref fbytes
    let (r1, transcript1) ← c.queries_OPEN
        aspis_core.digest.LegacyHashFn.Insts.Aspis_coreDigestDigest32
        transcript 31#u8 s9
    let cf1 ← PV_EVH_Prefix.lift (core.result.Result.Insts.CoreOpsTry.branch r1)
    match cf1 with
    | core.ops.control_flow.ControlFlow.Continue val1 =>
      let s10 ← PV_EVH_Prefix.lift (Aeneas.Std.lift (Array.to_slice (Std.Array.empty Std.U8)))
      let _ ← c.scalar_k_OPEN
          aspis_core.digest.LegacyHashFn.Insts.Aspis_coreDigestDigest32
          transcript1 32#u8 s10
      let scp ← PV_EVH_Prefix.lift (Array.index_usize prepared.sem.z 0#usize)
      let scp1 ← PV_EVH_Prefix.lift (Array.index_usize prepared.sem.z 1#usize)
      let s11 ← PV_EVH_Prefix.lift (Aeneas.Std.lift (Array.to_slice val1))
      let v ← c.toVec_OPEN core.clone.CloneU32 s11
      let a ← PV_EVH_Prefix.lift (Array.index_usize prepared.sem.roots 0#usize)
      let r2 ← c.public_check_OPEN variant
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
          } a
      let cf2 ← PV_EVH_Prefix.lift (core.result.Result.Insts.CoreOpsTry.branch r2)
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
        PV_EVH_Prefix.lift (core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
          prover.Publication (core.convert.FromSame verifier.Error) residual)
    | core.ops.control_flow.ControlFlow.Break residual =>
      PV_EVH_Prefix.lift (core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
        prover.Publication (core.convert.FromSame verifier.Error) residual)
  | core.ops.control_flow.ControlFlow.Break residual =>
    PV_EVH_Prefix.lift (core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
      prover.Publication (core.convert.FromSame verifier.Error) residual)

theorem run_fixed
  (variant : transport.Variant)
  (hash : Slice (Slice Std.U8) → Result (Array Std.U8 32#usize))
  (prepared : prover.PreparedOpening)
  (folded_salts : host_commitment.PrivateSalts) (c : Callees) (compatible : Compatible c) :
    FinishedView (run variant hash prepared folded_salts c) (prover.finish_opening variant hash prepared folded_salts) := by
  unfold run prover.finish_opening
  let s := alloc.vec.Vec.deref prepared.folded_word
  try dsimp only
  try dsimp only
  apply PV_EVH_Prefix.bind_fixed
  ·
    exact compatible.folded_leaves_fixed _ _ _
  · intro leaves
    try dsimp only
    apply PV_EVH_Prefix.bind_fixed
    ·
      exact compatible.new_fixed _ _ _
    · intro o
      try dsimp only
      apply PV_EVH_Prefix.bind_fixed
      ·
        exact compatible.op7_fixed _ _
      · intro r
        try dsimp only
        apply PV_EVH_Prefix.bind_fixed
        ·
          exact PV_EVH_Prefix.lift_fixed _
        · intro cf
          try dsimp only
          cases cf with
          | Continue val =>
            try dsimp only
            apply PV_EVH_Prefix.bind_fixed
            ·
              exact compatible.root_fixed _
            · intro root
              let s1 := alloc.vec.Vec.deref prepared.q1
              try dsimp only
              let s2 := alloc.vec.Vec.deref prepared.w1
              try dsimp only
              try dsimp only
              apply PV_EVH_Prefix.bind_fixed
              ·
                exact compatible.round_fixed _ _
              · intro c1
                try dsimp only
                apply PV_EVH_Prefix.bind_fixed
                ·
                  exact PV_EVH_Prefix.lift_fixed _
                · intro s3
                  try dsimp only
                  apply PV_EVH_Prefix.bind_fixed
                  ·
                    exact compatible.encoded_slice_fixed _
                  · intro c1bytes
                    try dsimp only
                    apply PV_EVH_Prefix.bind_fixed
                    ·
                      exact PV_EVH_Prefix.lift_fixed _
                    · intro s4
                      try dsimp only
                      apply PV_EVH_Prefix.bind_fixed
                      ·
                        exact compatible.toVec_fixed _ _
                      · intro payload
                        let s5 := alloc.vec.Vec.deref c1bytes
                        try dsimp only
                        try dsimp only
                        apply PV_EVH_Prefix.bind_fixed
                        ·
                          exact compatible.extendFromSlice_fixed _ _ _
                        · intro payload1
                          let s6 := alloc.vec.Vec.deref payload1
                          try dsimp only
                          try dsimp only
                          apply PV_EVH_Prefix.bind_fixed
                          ·
                            exact compatible.scalar_fixed _ _ _ _ _
                          · rintro ⟨alpha1, transcript⟩
                            let s7 := alloc.vec.Vec.deref prepared.q1
                            try dsimp only
                            try dsimp only
                            apply PV_EVH_Prefix.bind_fixed
                            ·
                              exact compatible.fold_fixed _ _ _
                            · intro final_message
                              let s8 := alloc.vec.Vec.deref final_message
                              try dsimp only
                              try dsimp only
                              apply PV_EVH_Prefix.bind_fixed
                              ·
                                exact compatible.encoded_slice_fixed _
                              · intro fbytes
                                let s9 := alloc.vec.Vec.deref fbytes
                                try dsimp only
                                try dsimp only
                                apply PV_EVH_Prefix.bind_fixed
                                ·
                                  exact compatible.queries_fixed _ _ _ _
                                · rintro ⟨r1, transcript1⟩
                                  try dsimp only
                                  apply PV_EVH_Prefix.bind_fixed
                                  ·
                                    exact PV_EVH_Prefix.lift_fixed _
                                  · intro cf1
                                    try dsimp only
                                    cases cf1 with
                                    | Continue val1 =>
                                      try dsimp only
                                      apply PV_EVH_Prefix.bind_fixed
                                      ·
                                        exact PV_EVH_Prefix.lift_fixed _
                                      · intro s10
                                        try dsimp only
                                        apply PV_EVH_Prefix.bind_fixed
                                        ·
                                          exact compatible.scalar_k_fixed _ _ _ _
                                        · intro _
                                          try dsimp only
                                          apply PV_EVH_Prefix.bind_fixed
                                          ·
                                            exact PV_EVH_Prefix.lift_fixed _
                                          · intro scp
                                            try dsimp only
                                            apply PV_EVH_Prefix.bind_fixed
                                            ·
                                              exact PV_EVH_Prefix.lift_fixed _
                                            · intro scp1
                                              try dsimp only
                                              apply PV_EVH_Prefix.bind_fixed
                                              ·
                                                exact PV_EVH_Prefix.lift_fixed _
                                              · intro s11
                                                try dsimp only
                                                apply PV_EVH_Prefix.bind_fixed
                                                ·
                                                  exact compatible.toVec_fixed _ _
                                                · intro v
                                                  try dsimp only
                                                  apply PV_EVH_Prefix.bind_fixed
                                                  ·
                                                    exact PV_EVH_Prefix.lift_fixed _
                                                  · intro a
                                                    try dsimp only
                                                    apply PV_EVH_Prefix.bind_fixed
                                                    ·
                                                      exact compatible.public_check_fixed _ _ _
                                                    · intro r2
                                                      try dsimp only
                                                      apply PV_EVH_Prefix.bind_fixed
                                                      ·
                                                        exact PV_EVH_Prefix.lift_fixed _
                                                      · intro cf2
                                                        try dsimp only
                                                        cases cf2 with
                                                        | Continue unused0 =>
                                                          exact PV_EVH_Prefix.lift_fixed _
                                                        | Break residual =>
                                                          exact PV_EVH_Prefix.lift_fixed _
                                    | Break residual =>
                                      exact PV_EVH_Prefix.lift_fixed _
          | Break residual =>
            exact PV_EVH_Prefix.lift_fixed _

#print axioms run_fixed
end PV_EVH_FinishOpening
