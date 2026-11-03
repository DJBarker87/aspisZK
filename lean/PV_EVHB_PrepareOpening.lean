import PV_EVH_Runtime
import PV_EVHB_CallbackSelection
set_option autoImplicit false
noncomputable section
namespace PV_EVHB_PrepareOpening
open Aeneas Aeneas.Std ProverRwFull PV_EVH_World
open PV_EVH_Runtime (Q PartialView)
variable [ExternalTypes] [ExternalFuns]

/-- Every non-language callee is explicitly OPEN. This structure supplies
neither a complete native event trace nor any successful run witness. -/
structure Callees where
  drop_OPEN : ∀ {T : Type}, T → Q Unit
  traitNe_OPEN : ∀ {T U : Type} (inst : core.cmp.PartialEq T U) (a : T) (b : U), Q (Bool)
  opening_coefficients_OPEN : ∀ (variant : transport.Variant)
  (messages : Slice (Array aspis_core.field.wide_exact.WideExact 1024#usize)), Q ((alloc.vec.Vec (Array aspis_core.field.wide_exact.WideExact
    1024#usize)))
  op45_OPEN : ∀ (arg0 : aspis_core.field.QM31), Q (aspis_core.field.wide_exact.WideExact)
  opening_claim_bytes_OPEN : ∀ (coefficients : Slice (Array aspis_core.field.wide_exact.WideExact
  1024#usize))
  (z1 : aspis_core.r0.domain.Point aspis_core.field.wide_exact.WideExact), Q ((alloc.vec.Vec Std.U8))
  state_OPEN : ∀ {H : Type} (aspis_coredigestDigest32Inst : aspis_core.digest.Digest32 H)
  (self : host_wire.SemanticTranscript H), Q ((Array Std.U8 32#usize))
  new_OPEN : ∀ {H : Type} (aspis_coredigestDigest32Inst : aspis_core.digest.Digest32 H)
  (hash : H) (semantic_state : Array Std.U8 32#usize)
  (variant : transport.Variant), Q ((host_transcript.Transcript H))
  scalar_OPEN : ∀ {H : Type} (aspis_coredigestDigest32Inst : aspis_core.digest.Digest32 H)
  (self : host_transcript.Transcript H) (row : Std.U8) (payload : Slice Std.U8)
  (nonzero : Bool), Q ((aspis_core.field.wide_exact.WideExact × (host_transcript.Transcript
    H)))
  opening_batch_OPEN : ∀ (coefficients : Slice (Array aspis_core.field.wide_exact.WideExact
  1024#usize)) (gamma : aspis_core.field.wide_exact.WideExact), Q ((alloc.vec.Vec aspis_core.field.wide_exact.WideExact))
  op252_OPEN : ∀ (arg0 : transport.Variant) (arg1 : (Array aspis_core.field.QM31 10#usize)) (arg2 : (Array aspis_core.circle.SecureCirclePoint 2#usize)), Q ((core.result.Result weights.Weights verifier.Error))
  opening_inactive_OPEN : ∀ (q : Slice aspis_core.field.wide_exact.WideExact) (w : weights.Weights), Q (aspis_core.field.wide_exact.WideExact)
  op51_OPEN : ∀ (arg0 : aspis_core.field.wide_exact.WideExact), Q ((Array Std.U8 32#usize))
  op251_OPEN : ∀ (arg0 : weights.Weights) (arg1 : aspis_core.field.wide_exact.WideExact), Q ((core.result.Result (alloc.vec.Vec aspis_core.field.wide_exact.WideExact) verifier.Error))
  round_OPEN : ∀ (q : Slice aspis_core.field.wide_exact.WideExact)
  (w : Slice aspis_core.field.wide_exact.WideExact), Q ((Array aspis_core.field.wide_exact.WideExact 7#usize))
  encoded_slice_OPEN : ∀ (values : Slice aspis_core.field.wide_exact.WideExact), Q ((alloc.vec.Vec Std.U8))
  fold_OPEN : ∀ (q : Slice aspis_core.field.wide_exact.WideExact)
  (alpha : aspis_core.field.wide_exact.WideExact) (dual : Bool), Q ((alloc.vec.Vec aspis_core.field.wide_exact.WideExact))
  evaluate_OPEN : ∀ {T : Type} (aspis_corer0scalarCodeFieldInst : aspis_core.r0.scalar.CodeField
  T) (self : host_commitment.EncodingDomain) (coefficients : Slice T)
  (depth : Std.Usize), Q ((core.result.Result (alloc.vec.Vec T) aspis_core.r0.Error))


structure Compatible (c : Callees) : Prop where
  drop_fixed : ∀ {T : Type} (value : T), PartialView (c.drop_OPEN value) (.ok ())
  traitNe_fixed : ∀ {T U : Type} (inst : core.cmp.PartialEq T U) (a : T) (b : U), PartialView (c.traitNe_OPEN inst a b) (core.cmp.PartialEq.ne.trait_default inst a b)
  opening_coefficients_fixed : ∀ (variant : transport.Variant)
  (messages : Slice (Array aspis_core.field.wide_exact.WideExact 1024#usize)), PartialView (c.opening_coefficients_OPEN variant messages) (prover.opening_coefficients variant messages)
  op45_fixed : ∀ (arg0 : aspis_core.field.QM31), PartialView (c.op45_OPEN arg0) (aspis_core.field.wide_exact.WideExact.from_qm31 arg0)
  opening_claim_bytes_fixed : ∀ (coefficients : Slice (Array aspis_core.field.wide_exact.WideExact
  1024#usize))
  (z1 : aspis_core.r0.domain.Point aspis_core.field.wide_exact.WideExact), PartialView (c.opening_claim_bytes_OPEN coefficients z1) (prover.opening_claim_bytes coefficients z1)
  state_fixed : ∀ {H : Type} (aspis_coredigestDigest32Inst : aspis_core.digest.Digest32 H)
  (self : host_wire.SemanticTranscript H), PartialView (c.state_OPEN aspis_coredigestDigest32Inst self) (host_wire.SemanticTranscript.impl.state aspis_coredigestDigest32Inst self)
  new_fixed : ∀ {H : Type} (aspis_coredigestDigest32Inst : aspis_core.digest.Digest32 H)
  (hash : H) (semantic_state : Array Std.U8 32#usize)
  (variant : transport.Variant), PartialView (c.new_OPEN aspis_coredigestDigest32Inst hash semantic_state variant) (host_transcript.Transcript.new aspis_coredigestDigest32Inst hash semantic_state variant)
  scalar_fixed : ∀ {H : Type} (aspis_coredigestDigest32Inst : aspis_core.digest.Digest32 H)
  (self : host_transcript.Transcript H) (row : Std.U8) (payload : Slice Std.U8)
  (nonzero : Bool), PartialView (c.scalar_OPEN aspis_coredigestDigest32Inst self row payload nonzero) (host_transcript.Transcript.scalar aspis_coredigestDigest32Inst self row payload nonzero)
  opening_batch_fixed : ∀ (coefficients : Slice (Array aspis_core.field.wide_exact.WideExact
  1024#usize)) (gamma : aspis_core.field.wide_exact.WideExact), PartialView (c.opening_batch_OPEN coefficients gamma) (prover.opening_batch coefficients gamma)
  op252_fixed : ∀ (arg0 : transport.Variant) (arg1 : (Array aspis_core.field.QM31 10#usize)) (arg2 : (Array aspis_core.circle.SecureCirclePoint 2#usize)), PartialView (c.op252_OPEN arg0 arg1 arg2) (weights.Weights.new arg0 arg1 arg2)
  opening_inactive_fixed : ∀ (q : Slice aspis_core.field.wide_exact.WideExact) (w : weights.Weights), PartialView (c.opening_inactive_OPEN q w) (prover.opening_inactive q w)
  op51_fixed : ∀ (arg0 : aspis_core.field.wide_exact.WideExact), PartialView (c.op51_OPEN arg0) (aspis_core.field.wide_exact.WideExact.to_le_bytes arg0)
  op251_fixed : ∀ (arg0 : weights.Weights) (arg1 : aspis_core.field.wide_exact.WideExact), PartialView (c.op251_OPEN arg0 arg1) (weights.Weights.materialize arg0 arg1)
  round_fixed : ∀ (q : Slice aspis_core.field.wide_exact.WideExact)
  (w : Slice aspis_core.field.wide_exact.WideExact), PartialView (c.round_OPEN q w) (prover.round q w)
  encoded_slice_fixed : ∀ (values : Slice aspis_core.field.wide_exact.WideExact), PartialView (c.encoded_slice_OPEN values) (prover.encoded_slice values)
  fold_fixed : ∀ (q : Slice aspis_core.field.wide_exact.WideExact)
  (alpha : aspis_core.field.wide_exact.WideExact) (dual : Bool), PartialView (c.fold_OPEN q alpha dual) (prover.fold q alpha dual)
  evaluate_fixed : ∀ {T : Type} (aspis_corer0scalarCodeFieldInst : aspis_core.r0.scalar.CodeField
  T) (self : host_commitment.EncodingDomain) (coefficients : Slice T)
  (depth : Std.Usize), PartialView (c.evaluate_OPEN aspis_corer0scalarCodeFieldInst self coefficients depth) (host_commitment.EncodingDomain.evaluate aspis_corer0scalarCodeFieldInst self coefficients depth)


def run
  (variant : transport.Variant)
  (hash : Slice (Slice Std.U8) → Result (Array Std.U8 32#usize))
  (backend : prover.Backend)
  (sem : host_semantic.BuiltSemantics aspis_core.digest.LegacyHashFn) (c : Callees) : Q (core.result.Result prover.PreparedOpening verifier.Error) := do
  let b ← c.traitNe_OPEN
      transport.Variant.Insts.CoreCmpPartialEqVariant variant
      transport.Variant.S2
  if b then
    pure (core.result.Result.Err verifier.Error.Semantic)
  else
    let s := alloc.vec.Vec.deref backend.messages
    let coefficients ← c.opening_coefficients_OPEN variant s
    let scp ← PV_EVH_Runtime.lift (Array.index_usize sem.z 1#usize)
    let we ← c.op45_OPEN scp.x
    let we1 ← c.op45_OPEN scp.y
    let s1 := alloc.vec.Vec.deref coefficients
    let y1 ← c.opening_claim_bytes_OPEN s1 { x := we, y := we1 }
    let a ← c.state_OPEN
        aspis_core.digest.LegacyHashFn.Insts.Aspis_coreDigestDigest32
        sem.transcript
    let transcript ← c.new_OPEN
        aspis_core.digest.LegacyHashFn.Insts.Aspis_coreDigestDigest32 hash a
        variant
    let s2 := alloc.vec.Vec.deref y1
    let (gamma, transcript1) ← c.scalar_OPEN
        aspis_core.digest.LegacyHashFn.Insts.Aspis_coreDigestDigest32
        transcript 27#u8 s2 true
    let s3 := alloc.vec.Vec.deref coefficients
    let q ← c.opening_batch_OPEN s3 gamma
    let r ← c.op252_OPEN variant sem.alpha sem.z
    let cf ← PV_EVH_Runtime.lift (core.result.Result.Insts.CoreOpsTry.branch r)
    match cf with
    | core.ops.control_flow.ControlFlow.Continue val =>
      let s4 := alloc.vec.Vec.deref q
      let inactive ← c.opening_inactive_OPEN s4 val
      let a1 ← c.op51_OPEN inactive
      let s5 ← PV_EVH_Runtime.lift (Aeneas.Std.lift (Array.to_slice a1))
      let (kappa, transcript2) ← c.scalar_OPEN
          aspis_core.digest.LegacyHashFn.Insts.Aspis_coreDigestDigest32
          transcript1 28#u8 s5 false
      let r1 ← c.op251_OPEN val kappa
      let cf1 ← PV_EVH_Runtime.lift (core.result.Result.Insts.CoreOpsTry.branch r1)
      match cf1 with
      | core.ops.control_flow.ControlFlow.Continue val1 =>
        let s6 := alloc.vec.Vec.deref q
        let s7 := alloc.vec.Vec.deref val1
        let c0 ← c.round_OPEN s6 s7
        let s8 ← PV_EVH_Runtime.lift (Aeneas.Std.lift (Array.to_slice c0))
        let c0bytes ← c.encoded_slice_OPEN s8
        let s9 := alloc.vec.Vec.deref c0bytes
        let (alpha0, transcript3) ← c.scalar_OPEN
            aspis_core.digest.LegacyHashFn.Insts.Aspis_coreDigestDigest32
            transcript2 29#u8 s9 false
        let s10 := alloc.vec.Vec.deref q
        let q1 ← c.fold_OPEN s10 alpha0 false
        let s11 := alloc.vec.Vec.deref val1
        let w1 ← c.fold_OPEN s11 alpha0 true
        let s12 := alloc.vec.Vec.deref q1
        let r2 ← c.evaluate_OPEN
            aspis_core.field.wide_exact.WideExact.Insts.Aspis_coreR0ScalarCodeField
            backend.domain s12 0#usize
        let r3 ← PV_EVHB_CallbackEffects.mapErr c.drop_OPEN c.drop_OPEN verifier.Error.Allocation r2 ()
        let cf2 ← PV_EVH_Runtime.lift (core.result.Result.Insts.CoreOpsTry.branch r3)
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
          PV_EVH_Runtime.lift (core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
            prover.PreparedOpening (core.convert.FromSame verifier.Error)
            residual)
      | core.ops.control_flow.ControlFlow.Break residual =>
        PV_EVH_Runtime.lift (core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
          prover.PreparedOpening (core.convert.FromSame verifier.Error)
          residual)
    | core.ops.control_flow.ControlFlow.Break residual =>
      PV_EVH_Runtime.lift (core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
        prover.PreparedOpening (core.convert.FromSame verifier.Error) residual)

theorem run_fixed
  (variant : transport.Variant)
  (hash : Slice (Slice Std.U8) → Result (Array Std.U8 32#usize))
  (backend : prover.Backend)
  (sem : host_semantic.BuiltSemantics aspis_core.digest.LegacyHashFn) (c : Callees) (compatible : Compatible c)
    (selected : PV_EVH_OperatorFrames.Selection (inferInstance : ExternalFuns)) :
    PartialView (run variant hash backend sem c) (prover.prepare_opening variant hash backend sem) := by
  unfold run prover.prepare_opening
  try dsimp only
  apply PV_EVH_Runtime.bind_view
  ·
    exact compatible.traitNe_fixed _ _ _
  · intro b
    by_cases condition : b
    · simp only [condition,if_true]
      exact PV_EVH_Runtime.lift_view _
    · simp only [condition,Bool.false_eq_true,if_false]
      let s := alloc.vec.Vec.deref backend.messages
      try dsimp only
      try dsimp only
      apply PV_EVH_Runtime.bind_view
      ·
        exact compatible.opening_coefficients_fixed _ _
      · intro coefficients
        try dsimp only
        apply PV_EVH_Runtime.bind_view
        ·
          exact PV_EVH_Runtime.lift_view _
        · intro scp
          try dsimp only
          apply PV_EVH_Runtime.bind_view
          ·
            exact compatible.op45_fixed _
          · intro we
            try dsimp only
            apply PV_EVH_Runtime.bind_view
            ·
              exact compatible.op45_fixed _
            · intro we1
              let s1 := alloc.vec.Vec.deref coefficients
              try dsimp only
              try dsimp only
              apply PV_EVH_Runtime.bind_view
              ·
                exact compatible.opening_claim_bytes_fixed _ _
              · intro y1
                try dsimp only
                apply PV_EVH_Runtime.bind_view
                ·
                  exact compatible.state_fixed _ _
                · intro a
                  try dsimp only
                  apply PV_EVH_Runtime.bind_view
                  ·
                    exact compatible.new_fixed _ _ _ _
                  · intro transcript
                    let s2 := alloc.vec.Vec.deref y1
                    try dsimp only
                    try dsimp only
                    apply PV_EVH_Runtime.bind_view
                    ·
                      exact compatible.scalar_fixed _ _ _ _ _
                    · rintro ⟨gamma, transcript1⟩
                      let s3 := alloc.vec.Vec.deref coefficients
                      try dsimp only
                      try dsimp only
                      apply PV_EVH_Runtime.bind_view
                      ·
                        exact compatible.opening_batch_fixed _ _
                      · intro q
                        try dsimp only
                        apply PV_EVH_Runtime.bind_view
                        ·
                          exact compatible.op252_fixed _ _ _
                        · intro r
                          try dsimp only
                          apply PV_EVH_Runtime.bind_view
                          ·
                            exact PV_EVH_Runtime.lift_view _
                          · intro cf
                            try dsimp only
                            cases cf with
                            | Continue val =>
                              let s4 := alloc.vec.Vec.deref q
                              try dsimp only
                              try dsimp only
                              apply PV_EVH_Runtime.bind_view
                              ·
                                exact compatible.opening_inactive_fixed _ _
                              · intro inactive
                                try dsimp only
                                apply PV_EVH_Runtime.bind_view
                                ·
                                  exact compatible.op51_fixed _
                                · intro a1
                                  try dsimp only
                                  apply PV_EVH_Runtime.bind_view
                                  ·
                                    exact PV_EVH_Runtime.lift_view _
                                  · intro s5
                                    try dsimp only
                                    apply PV_EVH_Runtime.bind_view
                                    ·
                                      exact compatible.scalar_fixed _ _ _ _ _
                                    · rintro ⟨kappa, transcript2⟩
                                      try dsimp only
                                      apply PV_EVH_Runtime.bind_view
                                      ·
                                        exact compatible.op251_fixed _ _
                                      · intro r1
                                        try dsimp only
                                        apply PV_EVH_Runtime.bind_view
                                        ·
                                          exact PV_EVH_Runtime.lift_view _
                                        · intro cf1
                                          try dsimp only
                                          cases cf1 with
                                          | Continue val1 =>
                                            let s6 := alloc.vec.Vec.deref q
                                            try dsimp only
                                            let s7 := alloc.vec.Vec.deref val1
                                            try dsimp only
                                            try dsimp only
                                            apply PV_EVH_Runtime.bind_view
                                            ·
                                              exact compatible.round_fixed _ _
                                            · intro c0
                                              try dsimp only
                                              apply PV_EVH_Runtime.bind_view
                                              ·
                                                exact PV_EVH_Runtime.lift_view _
                                              · intro s8
                                                try dsimp only
                                                apply PV_EVH_Runtime.bind_view
                                                ·
                                                  exact compatible.encoded_slice_fixed _
                                                · intro c0bytes
                                                  let s9 := alloc.vec.Vec.deref c0bytes
                                                  try dsimp only
                                                  try dsimp only
                                                  apply PV_EVH_Runtime.bind_view
                                                  ·
                                                    exact compatible.scalar_fixed _ _ _ _ _
                                                  · rintro ⟨alpha0, transcript3⟩
                                                    let s10 := alloc.vec.Vec.deref q
                                                    try dsimp only
                                                    try dsimp only
                                                    apply PV_EVH_Runtime.bind_view
                                                    ·
                                                      exact compatible.fold_fixed _ _ _
                                                    · intro q1
                                                      let s11 := alloc.vec.Vec.deref val1
                                                      try dsimp only
                                                      try dsimp only
                                                      apply PV_EVH_Runtime.bind_view
                                                      ·
                                                        exact compatible.fold_fixed _ _ _
                                                      · intro w1
                                                        let s12 := alloc.vec.Vec.deref q1
                                                        try dsimp only
                                                        try dsimp only
                                                        apply PV_EVH_Runtime.bind_view
                                                        ·
                                                          exact compatible.evaluate_fixed _ _ _ _
                                                        · intro r2
                                                          try dsimp only
                                                          apply PV_EVH_Runtime.bind_view
                                                          ·
                                                            change PartialView _ ((inferInstance : ExternalFuns).op12 _ _ _)
                                                            exact PV_EVHB_CallbackSelection.constructor_mapErr_view _ selected _ c.drop_OPEN c.drop_OPEN verifier.Error.Allocation () _ (fun _ => rfl)
                                                              (fun e => compatible.drop_fixed e) (compatible.drop_fixed ())
                                                          · intro r3
                                                            try dsimp only
                                                            apply PV_EVH_Runtime.bind_view
                                                            ·
                                                              exact PV_EVH_Runtime.lift_view _
                                                            · intro cf2
                                                              try dsimp only
                                                              cases cf2 with
                                                              | Continue val2 =>
                                                                exact PV_EVH_Runtime.lift_view _
                                                              | Break residual =>
                                                                exact PV_EVH_Runtime.lift_view _
                                          | Break residual =>
                                            exact PV_EVH_Runtime.lift_view _
                            | Break residual =>
                              exact PV_EVH_Runtime.lift_view _

#print axioms run_fixed
end PV_EVHB_PrepareOpening
