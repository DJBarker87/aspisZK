import PV_EVH_RuntimeValueBind
import PV_EVH_Runtime
import PV_EVHB_CallbackEffects
set_option autoImplicit false
noncomputable section
namespace PV_EVHB_PublishCompact
open Aeneas Aeneas.Std ProverRwFull PV_EVH_World
open PV_EVH_Runtime (Q PartialView)
variable [ExternalTypes] [ExternalFuns]

/-- Every non-language callee is explicitly OPEN. This structure supplies
neither a complete native event trace nor any successful run witness. -/
structure Callees where
  drop_OPEN : ∀ {T : Type}, T → Q Unit
  op242_OPEN : Q (Std.Usize)
  op245_OPEN : Q ((Array Std.U8 8#usize))
  extendFromSlice_OPEN : ∀ {T : Type} (inst : core.clone.Clone T) (v : alloc.vec.Vec T) (s : Slice T), Q (alloc.vec.Vec T)
  op234_OPEN : ∀ (arg0 : transport.Variant), Q (Std.U8)
  compact_semantic_OPEN : ∀ (logical : Slice Std.U8) (out : alloc.vec.Vec Std.U8), Q (((core.result.Result Unit compact.CodecError) × (alloc.vec.Vec
    Std.U8)))

  compact_values_OPEN : ∀ (logical : Slice Std.U8) (out : alloc.vec.Vec Std.U8), Q (((core.result.Result Unit compact.CodecError) × (alloc.vec.Vec
    Std.U8)))
  op51_OPEN : ∀ (arg0 : aspis_core.field.wide_exact.WideExact), Q ((Array Std.U8 32#usize))
  op244_OPEN : Q (Std.Usize)
  assert_OPEN : ∀ (condition : Prop) [Decidable condition], Q (Unit)
  unwrap_OPEN : ∀ {T : Type} (value : Option T), Q (T)
  append_query_openings_OPEN : ∀ (out : alloc.vec.Vec Std.U8) (cc1 : host_commitment.Commitment)
  (cc2 : host_commitment.Commitment) (queries : Array Std.U32 22#usize)
  (folded_word : Slice aspis_core.field.wide_exact.WideExact)
  (folded_salts : host_commitment.PrivateSalts), Q ((alloc.vec.Vec Std.U8))
  op243_OPEN : Q (Std.Usize)
  append_node_slots_OPEN : ∀ (out : alloc.vec.Vec Std.U8) (cc1 : host_commitment.Commitment)
  (cc2 : host_commitment.Commitment) (tree : host_tree.BinaryTree)
  (queries : Array Std.U32 22#usize), Q ((core.result.Result (alloc.vec.Vec Std.U8) verifier.Error))
  withCapacity_OPEN : ∀ (T : Type) (capacity : Usize), Q (alloc.vec.Vec T)

structure Compatible (c : Callees) : Prop where
  drop_fixed : ∀ {T : Type} (value : T), PartialView (c.drop_OPEN value) (.ok ())
  op242_fixed : PartialView (c.op242_OPEN) (compact.PROOF_BYTES)
  op245_fixed : PartialView (c.op245_OPEN) (compact.MAGIC)
  extendFromSlice_fixed : ∀ {T : Type} (inst : core.clone.Clone T) (v : alloc.vec.Vec T) (s : Slice T), PartialView (c.extendFromSlice_OPEN inst v s) (alloc.vec.Vec.extend_from_slice inst v s)
  op234_fixed : ∀ (arg0 : transport.Variant), PartialView (c.op234_OPEN arg0) (transport.Variant.tag arg0)
  compact_semantic_fixed : ∀ (logical : Slice Std.U8) (out : alloc.vec.Vec Std.U8), PartialView (c.compact_semantic_OPEN logical out) (host_compact.compact_semantic logical out)

  compact_values_fixed : ∀ (logical : Slice Std.U8) (out : alloc.vec.Vec Std.U8), PartialView (c.compact_values_OPEN logical out) (host_compact.compact_values logical out)
  op51_fixed : ∀ (arg0 : aspis_core.field.wide_exact.WideExact), PartialView (c.op51_OPEN arg0) (aspis_core.field.wide_exact.WideExact.to_le_bytes arg0)
  op244_fixed : PartialView (c.op244_OPEN) (compact.OFF_OPENINGS)
  assert_fixed : ∀ (condition : Prop) [Decidable condition], PartialView (c.assert_OPEN condition) (massert condition)
  unwrap_fixed : ∀ {T : Type} (value : Option T), PartialView (c.unwrap_OPEN value) (core.option.Option.unwrap value)
  append_query_openings_fixed : ∀ (out : alloc.vec.Vec Std.U8) (cc1 : host_commitment.Commitment)
  (cc2 : host_commitment.Commitment) (queries : Array Std.U32 22#usize)
  (folded_word : Slice aspis_core.field.wide_exact.WideExact)
  (folded_salts : host_commitment.PrivateSalts), PartialView (c.append_query_openings_OPEN out cc1 cc2 queries folded_word folded_salts) (prover.append_query_openings out cc1 cc2 queries folded_word folded_salts)
  op243_fixed : PartialView (c.op243_OPEN) (compact.OFF_NODES)
  append_node_slots_fixed : ∀ (out : alloc.vec.Vec Std.U8) (cc1 : host_commitment.Commitment)
  (cc2 : host_commitment.Commitment) (tree : host_tree.BinaryTree)
  (queries : Array Std.U32 22#usize), PartialView (c.append_node_slots_OPEN out cc1 cc2 tree queries) (prover.append_node_slots out cc1 cc2 tree queries)
  withCapacity_fixed : ∀ (T : Type) (capacity : Usize), PartialView (c.withCapacity_OPEN T capacity) (Result.ok (alloc.vec.Vec.with_capacity T capacity))

def run
  (variant : transport.Variant) (p : prover.Publication) (c : Callees) : Q (core.result.Result (alloc.vec.Vec Std.U8) verifier.Error) := do
  let i ← c.op242_OPEN
  let out ← c.withCapacity_OPEN Std.U8 i
  let a ← c.op245_OPEN
  let s ← PV_EVH_Runtime.lift (Aeneas.Std.lift (Array.to_slice a))
  let out1 ← c.extendFromSlice_OPEN core.clone.CloneU8 out s
  let i1 ← c.op234_OPEN variant
  let s1 ← PV_EVH_Runtime.lift (Aeneas.Std.lift (Array.to_slice
      (Array.make 8#usize [ i1, 0#u8, 0#u8, 0#u8, 0#u8, 0#u8, 0#u8, 0#u8 ])))
  let out2 ← c.extendFromSlice_OPEN core.clone.CloneU8 out1 s1
  let s2 := alloc.vec.Vec.deref p.semantic_bytes
  let (r, out3) ← c.compact_semantic_OPEN s2 out2
  let r1 ← PV_EVHB_CallbackEffects.mapErr c.drop_OPEN c.drop_OPEN verifier.Error.Semantic r ()
  let cf ← PV_EVH_Runtime.lift (core.result.Result.Insts.CoreOpsTry.branch r1)
  match cf with
  | core.ops.control_flow.ControlFlow.Continue _ =>
    let s3 := alloc.vec.Vec.deref p.y1
    let (r2, out4) ← c.compact_values_OPEN s3 out3
    let r3 ← PV_EVHB_CallbackEffects.mapErr c.drop_OPEN c.drop_OPEN verifier.Error.Semantic r2 ()
    let cf1 ← PV_EVH_Runtime.lift (core.result.Result.Insts.CoreOpsTry.branch r3)
    match cf1 with
    | core.ops.control_flow.ControlFlow.Continue _ =>
      let a1 ← c.op51_OPEN p.inactive
      let s4 ← PV_EVH_Runtime.lift (Aeneas.Std.lift (Array.to_slice a1))
      let out5 ← c.extendFromSlice_OPEN core.clone.CloneU8 out4 s4
      let s5 := alloc.vec.Vec.deref p.c0bytes
      let out6 ← c.extendFromSlice_OPEN core.clone.CloneU8 out5 s5
      let s6 ← PV_EVH_Runtime.lift (Aeneas.Std.lift (Array.to_slice p.root))
      let out7 ← c.extendFromSlice_OPEN core.clone.CloneU8 out6 s6
      let s7 := alloc.vec.Vec.deref p.c1bytes
      let out8 ← c.extendFromSlice_OPEN core.clone.CloneU8 out7 s7
      let s8 := alloc.vec.Vec.deref p.fbytes
      let out9 ← c.extendFromSlice_OPEN core.clone.CloneU8 out8 s8
      let left_val := alloc.vec.Vec.len out9
      let right_val ← c.op244_OPEN
      let _ ← c.assert_OPEN (left_val = right_val)
      let (o, _) := core.option.Option.take p.backend.c1
      let cc1 ← c.unwrap_OPEN o
      let (o1, _) := core.option.Option.take p.backend.c2
      let cc2 ← c.unwrap_OPEN o1
      let s9 := alloc.vec.Vec.deref p.folded_word
      let out10 ← c.append_query_openings_OPEN out9 cc1 cc2 p.queries s9 p.folded_salts
      let left_val1 := alloc.vec.Vec.len out10
      let right_val1 ← c.op243_OPEN
      let _ ← c.assert_OPEN (left_val1 = right_val1)
      let r4 ← c.append_node_slots_OPEN out10 cc1 cc2 p.tree p.queries
      let cf2 ← PV_EVH_Runtime.lift (core.result.Result.Insts.CoreOpsTry.branch r4)
      match cf2 with
      | core.ops.control_flow.ControlFlow.Continue val =>
        let left_val2 := alloc.vec.Vec.len val
        let _ ← c.assert_OPEN (left_val2 = i)
        pure (core.result.Result.Ok val)
      | core.ops.control_flow.ControlFlow.Break residual =>
        PV_EVH_Runtime.lift (core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
          (alloc.vec.Vec Std.U8) (core.convert.FromSame verifier.Error)
          residual)
    | core.ops.control_flow.ControlFlow.Break residual =>
      PV_EVH_Runtime.lift (core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
        (alloc.vec.Vec Std.U8) (core.convert.FromSame verifier.Error) residual)
  | core.ops.control_flow.ControlFlow.Break residual =>
    PV_EVH_Runtime.lift (core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
      (alloc.vec.Vec Std.U8) (core.convert.FromSame verifier.Error) residual)

theorem run_fixed
  (variant : transport.Variant) (p : prover.Publication) (c : Callees) (compatible : Compatible c) :
    PartialView (run variant p c) (prover.publish_compact variant p) := by
  unfold run prover.publish_compact
  try dsimp only
  apply PV_EVH_Runtime.bind_view
  ·
    exact compatible.op242_fixed
  · intro i
    apply PV_EVH_RuntimeValueBind.value_bind_fixed _ (alloc.vec.Vec.with_capacity Std.U8 i)
    · exact compatible.withCapacity_fixed _ _
    ·
      try dsimp only
      apply PV_EVH_Runtime.bind_view
      ·
        exact compatible.op245_fixed
      · intro a
        try dsimp only
        apply PV_EVH_Runtime.bind_view
        ·
          exact PV_EVH_Runtime.lift_view _
        · intro s
          try dsimp only
          apply PV_EVH_Runtime.bind_view
          ·
            exact compatible.extendFromSlice_fixed _ _ _
          · intro out1
            try dsimp only
            apply PV_EVH_Runtime.bind_view
            ·
              exact compatible.op234_fixed _
            · intro i1
              try dsimp only
              apply PV_EVH_Runtime.bind_view
              ·
                exact PV_EVH_Runtime.lift_view _
              · intro s1
                try dsimp only
                apply PV_EVH_Runtime.bind_view
                ·
                  exact compatible.extendFromSlice_fixed _ _ _
                · intro out2
                  let s2 := alloc.vec.Vec.deref p.semantic_bytes
                  try dsimp only
                  try dsimp only
                  apply PV_EVH_Runtime.bind_view
                  ·
                    exact compatible.compact_semantic_fixed _ _
                  · rintro ⟨r, out3⟩
                    try dsimp only
                    apply PV_EVH_Runtime.bind_view
                    ·
                      exact PV_EVHB_CallbackEffects.mapErr_view c.drop_OPEN c.drop_OPEN verifier.Error.Semantic () _
                        (fun e => compatible.drop_fixed e) (compatible.drop_fixed ())
                    · intro r1
                      try dsimp only
                      apply PV_EVH_Runtime.bind_view
                      ·
                        exact PV_EVH_Runtime.lift_view _
                      · intro cf
                        try dsimp only
                        cases cf with
                        | Continue unused0 =>
                          let s3 := alloc.vec.Vec.deref p.y1
                          try dsimp only
                          try dsimp only
                          apply PV_EVH_Runtime.bind_view
                          ·
                            exact compatible.compact_values_fixed _ _
                          · rintro ⟨r2, out4⟩
                            try dsimp only
                            apply PV_EVH_Runtime.bind_view
                            ·
                              exact PV_EVHB_CallbackEffects.mapErr_view c.drop_OPEN c.drop_OPEN verifier.Error.Semantic () _
                                (fun e => compatible.drop_fixed e) (compatible.drop_fixed ())
                            · intro r3
                              try dsimp only
                              apply PV_EVH_Runtime.bind_view
                              ·
                                exact PV_EVH_Runtime.lift_view _
                              · intro cf1
                                try dsimp only
                                cases cf1 with
                                | Continue unused0 =>
                                  try dsimp only
                                  apply PV_EVH_Runtime.bind_view
                                  ·
                                    exact compatible.op51_fixed _
                                  · intro a1
                                    try dsimp only
                                    apply PV_EVH_Runtime.bind_view
                                    ·
                                      exact PV_EVH_Runtime.lift_view _
                                    · intro s4
                                      try dsimp only
                                      apply PV_EVH_Runtime.bind_view
                                      ·
                                        exact compatible.extendFromSlice_fixed _ _ _
                                      · intro out5
                                        let s5 := alloc.vec.Vec.deref p.c0bytes
                                        try dsimp only
                                        try dsimp only
                                        apply PV_EVH_Runtime.bind_view
                                        ·
                                          exact compatible.extendFromSlice_fixed _ _ _
                                        · intro out6
                                          try dsimp only
                                          apply PV_EVH_Runtime.bind_view
                                          ·
                                            exact PV_EVH_Runtime.lift_view _
                                          · intro s6
                                            try dsimp only
                                            apply PV_EVH_Runtime.bind_view
                                            ·
                                              exact compatible.extendFromSlice_fixed _ _ _
                                            · intro out7
                                              let s7 := alloc.vec.Vec.deref p.c1bytes
                                              try dsimp only
                                              try dsimp only
                                              apply PV_EVH_Runtime.bind_view
                                              ·
                                                exact compatible.extendFromSlice_fixed _ _ _
                                              · intro out8
                                                let s8 := alloc.vec.Vec.deref p.fbytes
                                                try dsimp only
                                                try dsimp only
                                                apply PV_EVH_Runtime.bind_view
                                                ·
                                                  exact compatible.extendFromSlice_fixed _ _ _
                                                · intro out9
                                                  let left_val := alloc.vec.Vec.len out9
                                                  try dsimp only
                                                  try dsimp only
                                                  apply PV_EVH_Runtime.bind_view
                                                  ·
                                                    exact compatible.op244_fixed
                                                  · intro right_val
                                                    try dsimp only
                                                    apply PV_EVH_Runtime.bind_view
                                                    ·
                                                      exact compatible.assert_fixed _
                                                    · intro _
                                                      let (o, _) := core.option.Option.take p.backend.c1
                                                      try dsimp only
                                                      try dsimp only
                                                      apply PV_EVH_Runtime.bind_view
                                                      ·
                                                        exact compatible.unwrap_fixed _
                                                      · intro cc1
                                                        let (o1, _) := core.option.Option.take p.backend.c2
                                                        try dsimp only
                                                        try dsimp only
                                                        apply PV_EVH_Runtime.bind_view
                                                        ·
                                                          exact compatible.unwrap_fixed _
                                                        · intro cc2
                                                          let s9 := alloc.vec.Vec.deref p.folded_word
                                                          try dsimp only
                                                          try dsimp only
                                                          apply PV_EVH_Runtime.bind_view
                                                          ·
                                                            exact compatible.append_query_openings_fixed _ _ _ _ _ _
                                                          · intro out10
                                                            let left_val1 := alloc.vec.Vec.len out10
                                                            try dsimp only
                                                            try dsimp only
                                                            apply PV_EVH_Runtime.bind_view
                                                            ·
                                                              exact compatible.op243_fixed
                                                            · intro right_val1
                                                              try dsimp only
                                                              apply PV_EVH_Runtime.bind_view
                                                              ·
                                                                exact compatible.assert_fixed _
                                                              · intro _
                                                                try dsimp only
                                                                apply PV_EVH_Runtime.bind_view
                                                                ·
                                                                  exact compatible.append_node_slots_fixed _ _ _ _ _
                                                                · intro r4
                                                                  try dsimp only
                                                                  apply PV_EVH_Runtime.bind_view
                                                                  ·
                                                                    exact PV_EVH_Runtime.lift_view _
                                                                  · intro cf2
                                                                    try dsimp only
                                                                    cases cf2 with
                                                                    | Continue val =>
                                                                      let left_val2 := alloc.vec.Vec.len val
                                                                      try dsimp only
                                                                      try dsimp only
                                                                      apply PV_EVH_Runtime.bind_view
                                                                      ·
                                                                        exact compatible.assert_fixed _
                                                                      · intro _
                                                                        exact PV_EVH_Runtime.lift_view _
                                                                    | Break residual =>
                                                                      exact PV_EVH_Runtime.lift_view _
                                | Break residual =>
                                  exact PV_EVH_Runtime.lift_view _
                        | Break residual =>
                          exact PV_EVH_Runtime.lift_view _

#print axioms run_fixed
end PV_EVHB_PublishCompact
