import PV_EVH_Prefix
set_option autoImplicit false
noncomputable section
namespace PV_EVH_OpPrepareOpening
open Aeneas Aeneas.Std ProverRwFull PV_EVH_World
open PV_EVH_Prefix (P FinishedView)
variable [ExternalTypes] [ExternalFuns]

/-- Every non-language callee is explicitly OPEN. This structure supplies
neither a complete native event trace nor any successful run witness. -/
structure Callees where
  traitNe_OPEN : ∀ {T U : Type} (inst : core.cmp.PartialEq T U) (a : T) (b : U), P (Bool)
  opening_coefficients_OPEN : ∀ (variant : transport.Variant)
  (messages : Slice (Array aspis_core.field.wide_exact.WideExact 1024#usize)), P ((alloc.vec.Vec (Array aspis_core.field.wide_exact.WideExact
    1024#usize)))
  op45_OPEN : ∀ (arg0 : aspis_core.field.QM31), P (aspis_core.field.wide_exact.WideExact)
  opening_claim_bytes_OPEN : ∀ (coefficients : Slice (Array aspis_core.field.wide_exact.WideExact
  1024#usize))
  (z1 : aspis_core.r0.domain.Point aspis_core.field.wide_exact.WideExact), P ((alloc.vec.Vec Std.U8))
  state_OPEN : ∀ {H : Type} (aspis_coredigestDigest32Inst : aspis_core.digest.Digest32 H)
  (self : host_wire.SemanticTranscript H), P ((Array Std.U8 32#usize))
  new_OPEN : ∀ {H : Type} (aspis_coredigestDigest32Inst : aspis_core.digest.Digest32 H)
  (hash : H) (semantic_state : Array Std.U8 32#usize)
  (variant : transport.Variant), P ((host_transcript.Transcript H))
  scalar_OPEN : ∀ {H : Type} (aspis_coredigestDigest32Inst : aspis_core.digest.Digest32 H)
  (self : host_transcript.Transcript H) (row : Std.U8) (payload : Slice Std.U8)
  (nonzero : Bool), P ((aspis_core.field.wide_exact.WideExact × (host_transcript.Transcript
    H)))
  opening_batch_OPEN : ∀ (coefficients : Slice (Array aspis_core.field.wide_exact.WideExact
  1024#usize)) (gamma : aspis_core.field.wide_exact.WideExact), P ((alloc.vec.Vec aspis_core.field.wide_exact.WideExact))
  op252_OPEN : ∀ (arg0 : transport.Variant) (arg1 : (Array aspis_core.field.QM31 10#usize)) (arg2 : (Array aspis_core.circle.SecureCirclePoint 2#usize)), P ((core.result.Result weights.Weights verifier.Error))
  opening_inactive_OPEN : ∀ (q : Slice aspis_core.field.wide_exact.WideExact) (w : weights.Weights), P (aspis_core.field.wide_exact.WideExact)
  op51_OPEN : ∀ (arg0 : aspis_core.field.wide_exact.WideExact), P ((Array Std.U8 32#usize))
  op251_OPEN : ∀ (arg0 : weights.Weights) (arg1 : aspis_core.field.wide_exact.WideExact), P ((core.result.Result (alloc.vec.Vec aspis_core.field.wide_exact.WideExact) verifier.Error))
  round_OPEN : ∀ (q : Slice aspis_core.field.wide_exact.WideExact)
  (w : Slice aspis_core.field.wide_exact.WideExact), P ((Array aspis_core.field.wide_exact.WideExact 7#usize))
  encoded_slice_OPEN : ∀ (values : Slice aspis_core.field.wide_exact.WideExact), P ((alloc.vec.Vec Std.U8))
  fold_OPEN : ∀ (q : Slice aspis_core.field.wide_exact.WideExact)
  (alpha : aspis_core.field.wide_exact.WideExact) (dual : Bool), P ((alloc.vec.Vec aspis_core.field.wide_exact.WideExact))
  evaluate_OPEN : ∀ {T : Type} (aspis_corer0scalarCodeFieldInst : aspis_core.r0.scalar.CodeField
  T) (self : host_commitment.EncodingDomain) (coefficients : Slice T)
  (depth : Std.Usize), P ((core.result.Result (alloc.vec.Vec T) aspis_core.r0.Error))
  op12_OPEN : ∀ {T : Type} {E : Type} {F : Type} {O : Type} (opsfunctionFnOnceOTupleEFInst :
      core.ops.function.FnOnce O E F) (arg0 : (core.result.Result T E)) (arg1 : O), P ((core.result.Result T F))

structure Compatible (c : Callees) : Prop where
  traitNe_fixed : ∀ {T U : Type} (inst : core.cmp.PartialEq T U) (a : T) (b : U), FinishedView (c.traitNe_OPEN inst a b) (core.cmp.PartialEq.ne.trait_default inst a b)
  opening_coefficients_fixed : ∀ (variant : transport.Variant)
  (messages : Slice (Array aspis_core.field.wide_exact.WideExact 1024#usize)), FinishedView (c.opening_coefficients_OPEN variant messages) (prover.opening_coefficients variant messages)
  op45_fixed : ∀ (arg0 : aspis_core.field.QM31), FinishedView (c.op45_OPEN arg0) (aspis_core.field.wide_exact.WideExact.from_qm31 arg0)
  opening_claim_bytes_fixed : ∀ (coefficients : Slice (Array aspis_core.field.wide_exact.WideExact
  1024#usize))
  (z1 : aspis_core.r0.domain.Point aspis_core.field.wide_exact.WideExact), FinishedView (c.opening_claim_bytes_OPEN coefficients z1) (prover.opening_claim_bytes coefficients z1)
  state_fixed : ∀ {H : Type} (aspis_coredigestDigest32Inst : aspis_core.digest.Digest32 H)
  (self : host_wire.SemanticTranscript H), FinishedView (c.state_OPEN aspis_coredigestDigest32Inst self) (host_wire.SemanticTranscript.impl.state aspis_coredigestDigest32Inst self)
  new_fixed : ∀ {H : Type} (aspis_coredigestDigest32Inst : aspis_core.digest.Digest32 H)
  (hash : H) (semantic_state : Array Std.U8 32#usize)
  (variant : transport.Variant), FinishedView (c.new_OPEN aspis_coredigestDigest32Inst hash semantic_state variant) (host_transcript.Transcript.new aspis_coredigestDigest32Inst hash semantic_state variant)
  scalar_fixed : ∀ {H : Type} (aspis_coredigestDigest32Inst : aspis_core.digest.Digest32 H)
  (self : host_transcript.Transcript H) (row : Std.U8) (payload : Slice Std.U8)
  (nonzero : Bool), FinishedView (c.scalar_OPEN aspis_coredigestDigest32Inst self row payload nonzero) (host_transcript.Transcript.scalar aspis_coredigestDigest32Inst self row payload nonzero)
  opening_batch_fixed : ∀ (coefficients : Slice (Array aspis_core.field.wide_exact.WideExact
  1024#usize)) (gamma : aspis_core.field.wide_exact.WideExact), FinishedView (c.opening_batch_OPEN coefficients gamma) (prover.opening_batch coefficients gamma)
  op252_fixed : ∀ (arg0 : transport.Variant) (arg1 : (Array aspis_core.field.QM31 10#usize)) (arg2 : (Array aspis_core.circle.SecureCirclePoint 2#usize)), FinishedView (c.op252_OPEN arg0 arg1 arg2) (weights.Weights.new arg0 arg1 arg2)
  opening_inactive_fixed : ∀ (q : Slice aspis_core.field.wide_exact.WideExact) (w : weights.Weights), FinishedView (c.opening_inactive_OPEN q w) (prover.opening_inactive q w)
  op51_fixed : ∀ (arg0 : aspis_core.field.wide_exact.WideExact), FinishedView (c.op51_OPEN arg0) (aspis_core.field.wide_exact.WideExact.to_le_bytes arg0)
  op251_fixed : ∀ (arg0 : weights.Weights) (arg1 : aspis_core.field.wide_exact.WideExact), FinishedView (c.op251_OPEN arg0 arg1) (weights.Weights.materialize arg0 arg1)
  round_fixed : ∀ (q : Slice aspis_core.field.wide_exact.WideExact)
  (w : Slice aspis_core.field.wide_exact.WideExact), FinishedView (c.round_OPEN q w) (prover.round q w)
  encoded_slice_fixed : ∀ (values : Slice aspis_core.field.wide_exact.WideExact), FinishedView (c.encoded_slice_OPEN values) (prover.encoded_slice values)
  fold_fixed : ∀ (q : Slice aspis_core.field.wide_exact.WideExact)
  (alpha : aspis_core.field.wide_exact.WideExact) (dual : Bool), FinishedView (c.fold_OPEN q alpha dual) (prover.fold q alpha dual)
  evaluate_fixed : ∀ {T : Type} (aspis_corer0scalarCodeFieldInst : aspis_core.r0.scalar.CodeField
  T) (self : host_commitment.EncodingDomain) (coefficients : Slice T)
  (depth : Std.Usize), FinishedView (c.evaluate_OPEN aspis_corer0scalarCodeFieldInst self coefficients depth) (host_commitment.EncodingDomain.evaluate aspis_corer0scalarCodeFieldInst self coefficients depth)
  op12_fixed : ∀ {T : Type} {E : Type} {F : Type} {O : Type} (opsfunctionFnOnceOTupleEFInst :
      core.ops.function.FnOnce O E F) (arg0 : (core.result.Result T E)) (arg1 : O), FinishedView (c.op12_OPEN opsfunctionFnOnceOTupleEFInst arg0 arg1) (core.result.Result.map_err opsfunctionFnOnceOTupleEFInst arg0 arg1)

def run
  (variant : transport.Variant)
  (hash : Slice (Slice Std.U8) → Result (Array Std.U8 32#usize))
  (backend : prover.Backend)
  (sem : host_semantic.BuiltSemantics aspis_core.digest.LegacyHashFn) (c : Callees) : P (core.result.Result prover.PreparedOpening verifier.Error) := do
  let b ← c.traitNe_OPEN
      transport.Variant.Insts.CoreCmpPartialEqVariant variant
      transport.Variant.S2
  if b then
    pure (core.result.Result.Err verifier.Error.Semantic)
  else
    let s := alloc.vec.Vec.deref backend.messages
    let coefficients ← c.opening_coefficients_OPEN variant s
    let scp ← PV_EVH_Prefix.lift (Array.index_usize sem.z 1#usize)
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
    let cf ← PV_EVH_Prefix.lift (core.result.Result.Insts.CoreOpsTry.branch r)
    match cf with
    | core.ops.control_flow.ControlFlow.Continue val =>
      let s4 := alloc.vec.Vec.deref q
      let inactive ← c.opening_inactive_OPEN s4 val
      let a1 ← c.op51_OPEN inactive
      let s5 ← PV_EVH_Prefix.lift (Aeneas.Std.lift (Array.to_slice a1))
      let (kappa, transcript2) ← c.scalar_OPEN
          aspis_core.digest.LegacyHashFn.Insts.Aspis_coreDigestDigest32
          transcript1 28#u8 s5 false
      let r1 ← c.op251_OPEN val kappa
      let cf1 ← PV_EVH_Prefix.lift (core.result.Result.Insts.CoreOpsTry.branch r1)
      match cf1 with
      | core.ops.control_flow.ControlFlow.Continue val1 =>
        let s6 := alloc.vec.Vec.deref q
        let s7 := alloc.vec.Vec.deref val1
        let c0 ← c.round_OPEN s6 s7
        let s8 ← PV_EVH_Prefix.lift (Aeneas.Std.lift (Array.to_slice c0))
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
        let r3 ← c.op12_OPEN
            prover.prepare_opening.closure.Insts.CoreOpsFunctionFnOnceTupleErrorError
            r2 ()
        let cf2 ← PV_EVH_Prefix.lift (core.result.Result.Insts.CoreOpsTry.branch r3)
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
          PV_EVH_Prefix.lift (core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
            prover.PreparedOpening (core.convert.FromSame verifier.Error)
            residual)
      | core.ops.control_flow.ControlFlow.Break residual =>
        PV_EVH_Prefix.lift (core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
          prover.PreparedOpening (core.convert.FromSame verifier.Error)
          residual)
    | core.ops.control_flow.ControlFlow.Break residual =>
      PV_EVH_Prefix.lift (core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
        prover.PreparedOpening (core.convert.FromSame verifier.Error) residual)

theorem run_fixed
  (variant : transport.Variant)
  (hash : Slice (Slice Std.U8) → Result (Array Std.U8 32#usize))
  (backend : prover.Backend)
  (sem : host_semantic.BuiltSemantics aspis_core.digest.LegacyHashFn) (c : Callees) (compatible : Compatible c) :
    FinishedView (run variant hash backend sem c) (prover.prepare_opening variant hash backend sem) := by
  unfold run prover.prepare_opening
  try dsimp only
  apply PV_EVH_Prefix.bind_fixed
  ·
    exact compatible.traitNe_fixed _ _ _
  · intro b
    by_cases condition : b
    · simp only [condition,if_true]
      exact PV_EVH_Prefix.lift_fixed _
    · simp only [condition,Bool.false_eq_true,if_false]
      let s := alloc.vec.Vec.deref backend.messages
      try dsimp only
      try dsimp only
      apply PV_EVH_Prefix.bind_fixed
      ·
        exact compatible.opening_coefficients_fixed _ _
      · intro coefficients
        try dsimp only
        apply PV_EVH_Prefix.bind_fixed
        ·
          exact PV_EVH_Prefix.lift_fixed _
        · intro scp
          try dsimp only
          apply PV_EVH_Prefix.bind_fixed
          ·
            exact compatible.op45_fixed _
          · intro we
            try dsimp only
            apply PV_EVH_Prefix.bind_fixed
            ·
              exact compatible.op45_fixed _
            · intro we1
              let s1 := alloc.vec.Vec.deref coefficients
              try dsimp only
              try dsimp only
              apply PV_EVH_Prefix.bind_fixed
              ·
                exact compatible.opening_claim_bytes_fixed _ _
              · intro y1
                try dsimp only
                apply PV_EVH_Prefix.bind_fixed
                ·
                  exact compatible.state_fixed _ _
                · intro a
                  try dsimp only
                  apply PV_EVH_Prefix.bind_fixed
                  ·
                    exact compatible.new_fixed _ _ _ _
                  · intro transcript
                    let s2 := alloc.vec.Vec.deref y1
                    try dsimp only
                    try dsimp only
                    apply PV_EVH_Prefix.bind_fixed
                    ·
                      exact compatible.scalar_fixed _ _ _ _ _
                    · rintro ⟨gamma, transcript1⟩
                      let s3 := alloc.vec.Vec.deref coefficients
                      try dsimp only
                      try dsimp only
                      apply PV_EVH_Prefix.bind_fixed
                      ·
                        exact compatible.opening_batch_fixed _ _
                      · intro q
                        try dsimp only
                        apply PV_EVH_Prefix.bind_fixed
                        ·
                          exact compatible.op252_fixed _ _ _
                        · intro r
                          try dsimp only
                          apply PV_EVH_Prefix.bind_fixed
                          ·
                            exact PV_EVH_Prefix.lift_fixed _
                          · intro cf
                            try dsimp only
                            cases cf with
                            | Continue val =>
                              let s4 := alloc.vec.Vec.deref q
                              try dsimp only
                              try dsimp only
                              apply PV_EVH_Prefix.bind_fixed
                              ·
                                exact compatible.opening_inactive_fixed _ _
                              · intro inactive
                                try dsimp only
                                apply PV_EVH_Prefix.bind_fixed
                                ·
                                  exact compatible.op51_fixed _
                                · intro a1
                                  try dsimp only
                                  apply PV_EVH_Prefix.bind_fixed
                                  ·
                                    exact PV_EVH_Prefix.lift_fixed _
                                  · intro s5
                                    try dsimp only
                                    apply PV_EVH_Prefix.bind_fixed
                                    ·
                                      exact compatible.scalar_fixed _ _ _ _ _
                                    · rintro ⟨kappa, transcript2⟩
                                      try dsimp only
                                      apply PV_EVH_Prefix.bind_fixed
                                      ·
                                        exact compatible.op251_fixed _ _
                                      · intro r1
                                        try dsimp only
                                        apply PV_EVH_Prefix.bind_fixed
                                        ·
                                          exact PV_EVH_Prefix.lift_fixed _
                                        · intro cf1
                                          try dsimp only
                                          cases cf1 with
                                          | Continue val1 =>
                                            let s6 := alloc.vec.Vec.deref q
                                            try dsimp only
                                            let s7 := alloc.vec.Vec.deref val1
                                            try dsimp only
                                            try dsimp only
                                            apply PV_EVH_Prefix.bind_fixed
                                            ·
                                              exact compatible.round_fixed _ _
                                            · intro c0
                                              try dsimp only
                                              apply PV_EVH_Prefix.bind_fixed
                                              ·
                                                exact PV_EVH_Prefix.lift_fixed _
                                              · intro s8
                                                try dsimp only
                                                apply PV_EVH_Prefix.bind_fixed
                                                ·
                                                  exact compatible.encoded_slice_fixed _
                                                · intro c0bytes
                                                  let s9 := alloc.vec.Vec.deref c0bytes
                                                  try dsimp only
                                                  try dsimp only
                                                  apply PV_EVH_Prefix.bind_fixed
                                                  ·
                                                    exact compatible.scalar_fixed _ _ _ _ _
                                                  · rintro ⟨alpha0, transcript3⟩
                                                    let s10 := alloc.vec.Vec.deref q
                                                    try dsimp only
                                                    try dsimp only
                                                    apply PV_EVH_Prefix.bind_fixed
                                                    ·
                                                      exact compatible.fold_fixed _ _ _
                                                    · intro q1
                                                      let s11 := alloc.vec.Vec.deref val1
                                                      try dsimp only
                                                      try dsimp only
                                                      apply PV_EVH_Prefix.bind_fixed
                                                      ·
                                                        exact compatible.fold_fixed _ _ _
                                                      · intro w1
                                                        let s12 := alloc.vec.Vec.deref q1
                                                        try dsimp only
                                                        try dsimp only
                                                        apply PV_EVH_Prefix.bind_fixed
                                                        ·
                                                          exact compatible.evaluate_fixed _ _ _ _
                                                        · intro r2
                                                          try dsimp only
                                                          apply PV_EVH_Prefix.bind_fixed
                                                          ·
                                                            exact compatible.op12_fixed _ _ _
                                                          · intro r3
                                                            try dsimp only
                                                            apply PV_EVH_Prefix.bind_fixed
                                                            ·
                                                              exact PV_EVH_Prefix.lift_fixed _
                                                            · intro cf2
                                                              try dsimp only
                                                              cases cf2 with
                                                              | Continue val2 =>
                                                                exact PV_EVH_Prefix.lift_fixed _
                                                              | Break residual =>
                                                                exact PV_EVH_Prefix.lift_fixed _
                                          | Break residual =>
                                            exact PV_EVH_Prefix.lift_fixed _
                            | Break residual =>
                              exact PV_EVH_Prefix.lift_fixed _

#print axioms run_fixed
end PV_EVH_OpPrepareOpening
