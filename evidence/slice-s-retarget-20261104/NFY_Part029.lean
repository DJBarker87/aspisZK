import Lean
import NFY_Part028
import NFY_Part006
import NFY_Part025
import RPz7_S2K_DigestBytes
import NFY_Part005
import Aeneas

-- BEGIN copied NBN_AfterDecode04: lean/NBN_AfterDecode04.lean
set_option autoImplicit false
noncomputable section
namespace NFY_NBN_AfterDecode04
open Aeneas Aeneas.Std Result ControlFlow Error
open AspisR1TerminalDecoder pool_v1.pair_terminal NFY_NBN_AfterDecodeTypes

def run (decode : Decode) (bytes : Slice U8) (val1 val3 val5 val7 val9 : Array aspis_core.field.M31 8#usize) : Result (core.result.Result PoolV1PairVerifiedAfterstateV1 PoolV1PairVerifierTransportErrorV1) := do
  let s7 ← core.slice.index.Slice.index (core.slice.index.SliceIndexRangeUsizeSlice Std.U8) bytes { start := 176#usize, «end» := 208#usize }
  let r15 ← pool_v1.pair_terminal.exact 32#usize s7
  let cf10 ← core.result.Result.Insts.CoreOpsTry.branch r15
  match cf10 with
  | core.ops.control_flow.ControlFlow.Continue val10 =>
    let r16 ← decode val10
    let r17 ← AspisR1TerminalDecoder.core.result.Result.map_err pool_v1.pair_terminal.decode_pool_v1_pair_verified_afterstate_v1.closure_5.Insts.CoreOpsFunctionFnOnceTupleAtomicStatementErrorPoolV1PairVerifierTransportErrorV1 r16 ()
    let cf11 ← core.result.Result.Insts.CoreOpsTry.branch r17
    match cf11 with
    | core.ops.control_flow.ControlFlow.Continue val11 =>
      let s8 ← core.slice.index.Slice.index (core.slice.index.SliceIndexRangeUsizeSlice Std.U8) bytes { start := 208#usize, «end» := 240#usize }
      let r18 ← pool_v1.pair_terminal.exact 32#usize s8
      let cf12 ← core.result.Result.Insts.CoreOpsTry.branch r18
      match cf12 with
      | core.ops.control_flow.ControlFlow.Continue val12 =>
        let r19 ← decode val12
        let r20 ← AspisR1TerminalDecoder.core.result.Result.map_err pool_v1.pair_terminal.decode_pool_v1_pair_verified_afterstate_v1.closure_6.Insts.CoreOpsFunctionFnOnceTupleAtomicStatementErrorPoolV1PairVerifierTransportErrorV1 r19 ()
        let cf13 ← core.result.Result.Insts.CoreOpsTry.branch r20
        match cf13 with
        | core.ops.control_flow.ControlFlow.Continue val13 =>
          let s9 ← core.slice.index.Slice.index (core.slice.index.SliceIndexRangeUsizeSlice Std.U8) bytes { start := 240#usize, «end» := 272#usize }
          let r21 ← pool_v1.pair_terminal.exact 32#usize s9
          let cf14 ← core.result.Result.Insts.CoreOpsTry.branch r21
          match cf14 with
          | core.ops.control_flow.ControlFlow.Continue val14 =>
            let r22 ← decode val14
            let r23 ← AspisR1TerminalDecoder.core.result.Result.map_err pool_v1.pair_terminal.decode_pool_v1_pair_verified_afterstate_v1.closure_7.Insts.CoreOpsFunctionFnOnceTupleAtomicStatementErrorPoolV1PairVerifierTransportErrorV1 r22 ()
            let cf15 ← core.result.Result.Insts.CoreOpsTry.branch r23
            match cf15 with
            | core.ops.control_flow.ControlFlow.Continue val15 =>
              let s10 ← core.slice.index.Slice.index (core.slice.index.SliceIndexRangeUsizeSlice Std.U8) bytes { start := 272#usize, «end» := 304#usize }
              let r24 ← pool_v1.pair_terminal.exact 32#usize s10
              let cf16 ← core.result.Result.Insts.CoreOpsTry.branch r24
              match cf16 with
              | core.ops.control_flow.ControlFlow.Continue val16 =>
                let r25 ← decode val16
                let r26 ← AspisR1TerminalDecoder.core.result.Result.map_err pool_v1.pair_terminal.decode_pool_v1_pair_verified_afterstate_v1.closure_8.Insts.CoreOpsFunctionFnOnceTupleAtomicStatementErrorPoolV1PairVerifierTransportErrorV1 r25 ()
                let cf17 ← core.result.Result.Insts.CoreOpsTry.branch r26
                match cf17 with
                | core.ops.control_flow.ControlFlow.Continue val17 =>
                  NFY_NBN_AfterDecode08.run decode bytes val1 val3 val5 val7 val9 val11 val13 val15 val17
                | core.ops.control_flow.ControlFlow.Break residual => core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual pool_v1.pair_terminal.PoolV1PairVerifiedAfterstateV1 (core.convert.FromSame pool_v1.pair_terminal.PoolV1PairVerifierTransportErrorV1) residual
              | core.ops.control_flow.ControlFlow.Break residual => core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual pool_v1.pair_terminal.PoolV1PairVerifiedAfterstateV1 (core.convert.FromSame pool_v1.pair_terminal.PoolV1PairVerifierTransportErrorV1) residual
            | core.ops.control_flow.ControlFlow.Break residual => core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual pool_v1.pair_terminal.PoolV1PairVerifiedAfterstateV1 (core.convert.FromSame pool_v1.pair_terminal.PoolV1PairVerifierTransportErrorV1) residual
          | core.ops.control_flow.ControlFlow.Break residual => core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual pool_v1.pair_terminal.PoolV1PairVerifiedAfterstateV1 (core.convert.FromSame pool_v1.pair_terminal.PoolV1PairVerifierTransportErrorV1) residual
        | core.ops.control_flow.ControlFlow.Break residual => core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual pool_v1.pair_terminal.PoolV1PairVerifiedAfterstateV1 (core.convert.FromSame pool_v1.pair_terminal.PoolV1PairVerifierTransportErrorV1) residual
      | core.ops.control_flow.ControlFlow.Break residual => core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual pool_v1.pair_terminal.PoolV1PairVerifiedAfterstateV1 (core.convert.FromSame pool_v1.pair_terminal.PoolV1PairVerifierTransportErrorV1) residual
    | core.ops.control_flow.ControlFlow.Break residual => core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual pool_v1.pair_terminal.PoolV1PairVerifiedAfterstateV1 (core.convert.FromSame pool_v1.pair_terminal.PoolV1PairVerifierTransportErrorV1) residual
  | core.ops.control_flow.ControlFlow.Break residual => core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual pool_v1.pair_terminal.PoolV1PairVerifiedAfterstateV1 (core.convert.FromSame pool_v1.pair_terminal.PoolV1PairVerifierTransportErrorV1) residual

theorem source (decode : Decode) (lower : NBN_Dep_DigestDecode decode)
    (bytes : Slice U8) (val1 val3 val5 val7 val9 : Array aspis_core.field.M31 8#usize) :
    run decode bytes val1 val3 val5 val7 val9 = AspisS6NativeAfterstateDecoderFactored.part_4 bytes val1 val3 val5 val7 val9 := by
  have same : decode = atomic_statement.decode_digest_canonical := funext lower
  unfold run
  simp only [NFY_NBN_AfterDecode08.source decode lower]
  rw [same]
  unfold AspisS6NativeAfterstateDecoderFactored.part_4
  run_tac do
    for _ in [:8] do
      let g ← Lean.Elab.Tactic.getMainGoal
      let t ← g.getType
      let names := t.getUsedConstants.filter fun n =>
        let s := n.toString
        (s.startsWith "NFY_NBN_AfterDecode" || s.startsWith "AspisS6NativeAfterstateDecoderFactored.") &&
        (s.splitOn ".").any (fun c => c.startsWith "match_")
      if names.isEmpty then break
      let ids := names.map Lean.mkIdent
      Lean.Elab.Tactic.evalTactic (← `(tactic| unfold $[$ids:ident]*))
  dsimp only
  all_goals with_reducible rfl

#print axioms source
end NFY_NBN_AfterDecode04
-- END copied NBN_AfterDecode04
-- BEGIN copied NBN_AfterDecode00: lean/NBN_AfterDecode00.lean
set_option autoImplicit false
noncomputable section
namespace NFY_NBN_AfterDecode00
open Aeneas Aeneas.Std Result ControlFlow Error
open AspisR1TerminalDecoder pool_v1.pair_terminal NFY_NBN_AfterDecodeTypes

def run (decode : Decode) (bytes : Slice U8) (val1 : Array aspis_core.field.M31 8#usize) : Result (core.result.Result PoolV1PairVerifiedAfterstateV1 PoolV1PairVerifierTransportErrorV1) := do
  let s3 ← core.slice.index.Slice.index (core.slice.index.SliceIndexRangeUsizeSlice Std.U8) bytes { start := 48#usize, «end» := 80#usize }
  let r3 ← pool_v1.pair_terminal.exact 32#usize s3
  let cf2 ← core.result.Result.Insts.CoreOpsTry.branch r3
  match cf2 with
  | core.ops.control_flow.ControlFlow.Continue val2 =>
    let r4 ← decode val2
    let r5 ← AspisR1TerminalDecoder.core.result.Result.map_err pool_v1.pair_terminal.decode_pool_v1_pair_verified_afterstate_v1.closure_1.Insts.CoreOpsFunctionFnOnceTupleAtomicStatementErrorPoolV1PairVerifierTransportErrorV1 r4 ()
    let cf3 ← core.result.Result.Insts.CoreOpsTry.branch r5
    match cf3 with
    | core.ops.control_flow.ControlFlow.Continue val3 =>
      let s4 ← core.slice.index.Slice.index (core.slice.index.SliceIndexRangeUsizeSlice Std.U8) bytes { start := 80#usize, «end» := 112#usize }
      let r6 ← pool_v1.pair_terminal.exact 32#usize s4
      let cf4 ← core.result.Result.Insts.CoreOpsTry.branch r6
      match cf4 with
      | core.ops.control_flow.ControlFlow.Continue val4 =>
        let r7 ← decode val4
        let r8 ← AspisR1TerminalDecoder.core.result.Result.map_err pool_v1.pair_terminal.decode_pool_v1_pair_verified_afterstate_v1.closure_2.Insts.CoreOpsFunctionFnOnceTupleAtomicStatementErrorPoolV1PairVerifierTransportErrorV1 r7 ()
        let cf5 ← core.result.Result.Insts.CoreOpsTry.branch r8
        match cf5 with
        | core.ops.control_flow.ControlFlow.Continue val5 =>
          let s5 ← core.slice.index.Slice.index (core.slice.index.SliceIndexRangeUsizeSlice Std.U8) bytes { start := 112#usize, «end» := 144#usize }
          let r9 ← pool_v1.pair_terminal.exact 32#usize s5
          let cf6 ← core.result.Result.Insts.CoreOpsTry.branch r9
          match cf6 with
          | core.ops.control_flow.ControlFlow.Continue val6 =>
            let r10 ← decode val6
            let r11 ← AspisR1TerminalDecoder.core.result.Result.map_err pool_v1.pair_terminal.decode_pool_v1_pair_verified_afterstate_v1.closure_3.Insts.CoreOpsFunctionFnOnceTupleAtomicStatementErrorPoolV1PairVerifierTransportErrorV1 r10 ()
            let cf7 ← core.result.Result.Insts.CoreOpsTry.branch r11
            match cf7 with
            | core.ops.control_flow.ControlFlow.Continue val7 =>
              let s6 ← core.slice.index.Slice.index (core.slice.index.SliceIndexRangeUsizeSlice Std.U8) bytes { start := 144#usize, «end» := 176#usize }
              let r12 ← pool_v1.pair_terminal.exact 32#usize s6
              let cf8 ← core.result.Result.Insts.CoreOpsTry.branch r12
              match cf8 with
              | core.ops.control_flow.ControlFlow.Continue val8 =>
                let r13 ← decode val8
                let r14 ← AspisR1TerminalDecoder.core.result.Result.map_err pool_v1.pair_terminal.decode_pool_v1_pair_verified_afterstate_v1.closure_4.Insts.CoreOpsFunctionFnOnceTupleAtomicStatementErrorPoolV1PairVerifierTransportErrorV1 r13 ()
                let cf9 ← core.result.Result.Insts.CoreOpsTry.branch r14
                match cf9 with
                | core.ops.control_flow.ControlFlow.Continue val9 =>
                  NFY_NBN_AfterDecode04.run decode bytes val1 val3 val5 val7 val9
                | core.ops.control_flow.ControlFlow.Break residual => core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual pool_v1.pair_terminal.PoolV1PairVerifiedAfterstateV1 (core.convert.FromSame pool_v1.pair_terminal.PoolV1PairVerifierTransportErrorV1) residual
              | core.ops.control_flow.ControlFlow.Break residual => core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual pool_v1.pair_terminal.PoolV1PairVerifiedAfterstateV1 (core.convert.FromSame pool_v1.pair_terminal.PoolV1PairVerifierTransportErrorV1) residual
            | core.ops.control_flow.ControlFlow.Break residual => core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual pool_v1.pair_terminal.PoolV1PairVerifiedAfterstateV1 (core.convert.FromSame pool_v1.pair_terminal.PoolV1PairVerifierTransportErrorV1) residual
          | core.ops.control_flow.ControlFlow.Break residual => core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual pool_v1.pair_terminal.PoolV1PairVerifiedAfterstateV1 (core.convert.FromSame pool_v1.pair_terminal.PoolV1PairVerifierTransportErrorV1) residual
        | core.ops.control_flow.ControlFlow.Break residual => core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual pool_v1.pair_terminal.PoolV1PairVerifiedAfterstateV1 (core.convert.FromSame pool_v1.pair_terminal.PoolV1PairVerifierTransportErrorV1) residual
      | core.ops.control_flow.ControlFlow.Break residual => core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual pool_v1.pair_terminal.PoolV1PairVerifiedAfterstateV1 (core.convert.FromSame pool_v1.pair_terminal.PoolV1PairVerifierTransportErrorV1) residual
    | core.ops.control_flow.ControlFlow.Break residual => core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual pool_v1.pair_terminal.PoolV1PairVerifiedAfterstateV1 (core.convert.FromSame pool_v1.pair_terminal.PoolV1PairVerifierTransportErrorV1) residual
  | core.ops.control_flow.ControlFlow.Break residual => core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual pool_v1.pair_terminal.PoolV1PairVerifiedAfterstateV1 (core.convert.FromSame pool_v1.pair_terminal.PoolV1PairVerifierTransportErrorV1) residual

theorem source (decode : Decode) (lower : NBN_Dep_DigestDecode decode)
    (bytes : Slice U8) (val1 : Array aspis_core.field.M31 8#usize) :
    run decode bytes val1 = AspisS6NativeAfterstateDecoderFactored.part_0 bytes val1 := by
  have same : decode = atomic_statement.decode_digest_canonical := funext lower
  unfold run
  simp only [NFY_NBN_AfterDecode04.source decode lower]
  rw [same]
  unfold AspisS6NativeAfterstateDecoderFactored.part_0
  run_tac do
    for _ in [:8] do
      let g ← Lean.Elab.Tactic.getMainGoal
      let t ← g.getType
      let names := t.getUsedConstants.filter fun n =>
        let s := n.toString
        (s.startsWith "NFY_NBN_AfterDecode" || s.startsWith "AspisS6NativeAfterstateDecoderFactored.") &&
        (s.splitOn ".").any (fun c => c.startsWith "match_")
      if names.isEmpty then break
      let ids := names.map Lean.mkIdent
      Lean.Elab.Tactic.evalTactic (← `(tactic| unfold $[$ids:ident]*))
  dsimp only
  all_goals with_reducible rfl

#print axioms source
end NFY_NBN_AfterDecode00
-- END copied NBN_AfterDecode00
-- BEGIN copied NBN_AfterDecodeParent: lean/NBN_AfterDecodeParent.lean
set_option autoImplicit false
noncomputable section
namespace NFY_NBN_AfterDecodeParent
open Aeneas Aeneas.Std Result ControlFlow Error
open AspisR1TerminalDecoder pool_v1.pair_terminal NFY_NBN_AfterDecodeTypes

def run (child : Decode) (bytes : Slice U8) : Result (core.result.Result PoolV1PairVerifiedAfterstateV1 PoolV1PairVerifierTransportErrorV1) := do
  let i := Slice.len bytes
  let i1 ← pool_v1.pair_terminal.POOL_V1_PAIR_VERIFIED_AFTERSTATE_BYTES
  if i != i1
  then ok (core.result.Result.Err pool_v1.pair_terminal.PoolV1PairVerifierTransportErrorV1.WrongLength)
  else
    let s ← core.slice.index.Slice.index (core.slice.index.SliceIndexRangeToUsizeSlice Std.U8) bytes { «end» := 4#usize }
    let s1 ← core.array.Array.index (core.ops.index.IndexSlice (core.slice.index.SliceIndexRangeUsizeSlice Std.U8)) pool_v1.pair_terminal.POOL_V1_PAIR_VERIFIED_AFTERSTATE_MAGIC { start := 0#usize, «end» := 4#usize }
    let b ← core.cmp.PartialEq.ne.trait_default (Slice.Insts.CoreCmpPartialEqSlice core.cmp.PartialEqU8) s s1
    if b
    then ok (core.result.Result.Err pool_v1.pair_terminal.PoolV1PairVerifierTransportErrorV1.WrongMagic)
    else
      let i2 ← Slice.index_usize bytes 4#usize
      if i2 != pool_v1.pair_terminal.POOL_V1_PAIR_VERIFIER_TRANSPORT_VERSION
      then ok (core.result.Result.Err pool_v1.pair_terminal.PoolV1PairVerifierTransportErrorV1.WrongVersion)
      else
        let i3 ← Slice.index_usize bytes 5#usize
        if i3 != pool_v1.pair_tree_profile.POOL_V1_PAIR_TREE_STORAGE_FORMAT_VERSION
        then ok (core.result.Result.Err pool_v1.pair_terminal.PoolV1PairVerifierTransportErrorV1.WrongPairFormat)
        else
          let i4 ← Slice.index_usize bytes 6#usize
          if i4 != pool_v1.format.POOL_V1_DIGEST_ENCODING_VERSION
          then ok (core.result.Result.Err pool_v1.pair_terminal.PoolV1PairVerifierTransportErrorV1.WrongDigestEncoding)
          else
            let i5 ← Slice.index_usize bytes 7#usize
            if i5 != 1#u8
            then ok (core.result.Result.Err pool_v1.pair_terminal.PoolV1PairVerifierTransportErrorV1.WrongSuccessCode)
            else
              let s2 ← core.slice.index.Slice.index (core.slice.index.SliceIndexRangeUsizeSlice Std.U8) bytes { start := 16#usize, «end» := 48#usize }
              let r ← pool_v1.pair_terminal.exact 32#usize s2
              let cf ← core.result.Result.Insts.CoreOpsTry.branch r
              match cf with
              | core.ops.control_flow.ControlFlow.Continue val =>
                let r1 ← child val
                let r2 ← AspisR1TerminalDecoder.core.result.Result.map_err pool_v1.pair_terminal.decode_pool_v1_pair_verified_afterstate_v1.closure.Insts.CoreOpsFunctionFnOnceTupleAtomicStatementErrorPoolV1PairVerifierTransportErrorV1 r1 ()
                let cf1 ← core.result.Result.Insts.CoreOpsTry.branch r2
                match cf1 with
                | core.ops.control_flow.ControlFlow.Continue val1 =>
                  NFY_NBN_AfterDecode00.run child bytes val1
                | core.ops.control_flow.ControlFlow.Break residual => core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual pool_v1.pair_terminal.PoolV1PairVerifiedAfterstateV1 (core.convert.FromSame pool_v1.pair_terminal.PoolV1PairVerifierTransportErrorV1) residual
              | core.ops.control_flow.ControlFlow.Break residual => core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual pool_v1.pair_terminal.PoolV1PairVerifiedAfterstateV1 (core.convert.FromSame pool_v1.pair_terminal.PoolV1PairVerifierTransportErrorV1) residual

theorem source (child : Decode) (lower : NBN_Dep_DigestDecode child) (bytes : Slice U8) :
    run child bytes = decode_pool_v1_pair_verified_afterstate_v1 bytes := by
  have factored : run child bytes = AspisS6NativeAfterstateDecoderFactored.decode bytes := by
    have same : child = atomic_statement.decode_digest_canonical := funext lower
    unfold run
    simp only [NFY_NBN_AfterDecode00.source child lower]
    rw [same]
    unfold AspisS6NativeAfterstateDecoderFactored.decode
    run_tac do
      for _ in [:8] do
        let g ← Lean.Elab.Tactic.getMainGoal
        let t ← g.getType
        let names := t.getUsedConstants.filter fun n =>
          let s := n.toString
          (s.startsWith "NFY_NBN_AfterDecode" || s.startsWith "AspisS6NativeAfterstateDecoderFactored.") &&
          (s.splitOn ".").any (fun c => c.startsWith "match_")
        if names.isEmpty then break
        let ids := names.map Lean.mkIdent
        Lean.Elab.Tactic.evalTactic (← `(tactic| unfold $[$ids:ident]*))
    dsimp only
    all_goals with_reducible rfl
  exact factored.trans (AspisS6NativeAfterstateDecoderFactored.decode_source bytes)

#print axioms source
end NFY_NBN_AfterDecodeParent
-- END copied NBN_AfterDecodeParent
-- BEGIN copied NBN_AfterstateDecoderDependency: lean/NBN_AfterstateDecoderDependency.lean
set_option autoImplicit false
noncomputable section
namespace NFY_NBN_AfterstateDecoderDependency
open Aeneas Aeneas.Std Result AspisR1TerminalDecoder
abbrev Decode := NFY_NBN_AfterDecodeTypes.Decode
abbrev NBN_Dep_DigestDecode := NFY_NBN_AfterDecodeTypes.NBN_Dep_DigestDecode
abbrev run := NFY_NBN_AfterDecodeParent.run

theorem source (decode : Decode) (lower : NBN_Dep_DigestDecode decode) (bytes : Slice U8) :
    run decode bytes = pool_v1.pair_terminal.decode_pool_v1_pair_verified_afterstate_v1 bytes :=
  NFY_NBN_AfterDecodeParent.source decode lower bytes

#print axioms source
end NFY_NBN_AfterstateDecoderDependency
-- END copied NBN_AfterstateDecoderDependency
-- BEGIN copied NBN_IteratorAssociation: lean/NBN_IteratorAssociation.lean
set_option autoImplicit false
namespace NFY_NBN_IteratorAssociation
open Aeneas Aeneas.Std Result
open AspisR1.S2K AspisR1.S2K.LoopStep
abbrev Rows := Array Digest 20#usize
abbrev Observation := Option (Nat × Digest) × Nat × Nat

def observe (out : Option (Usize × Digest) × Iter) : Observation :=
  (out.1.map (fun (k,d) => (k.val,d)),out.2.count.val,
    out.2.iter.slice.length - out.2.iter.i)

def projected (rows : Rows) (k : Usize) : Result Observation := do
  let step ← next (Iterator.cursor rows k)
  ok (observe step)

/-- Same index/row/next_index/remaining tuple as the native one-step K009 gate. -/
theorem next_row (rows : Rows) (k : Usize) (bound : k.val < 20) :
    projected rows k = ok
      (some (k.val,rows.val[k.val]'(by have := rows.property; scalar_tac)),
       k.val+1,19-k.val) := by
  rw [projected,Iterator.next_row rows k bound]
  simp only [bind_tc_ok,observe,Option.map_some,Iterator.cursor,
    Slice.length,Array.to_slice,rows.property]
  simp [Aeneas.Std.uncurry]

theorem exhausted (rows : Rows) : projected rows 20#usize = ok (none,20,0) := by
  rw [projected,Iterator.exhausted]
  simp [observe,Iterator.cursor,Slice.length,Array.to_slice,rows.property]

#print axioms next_row
#print axioms exhausted
end NFY_NBN_IteratorAssociation
-- END copied NBN_IteratorAssociation
-- BEGIN copied NBN_U03: lean/NBN_U03.lean
set_option autoImplicit false
noncomputable section
namespace NFY_NBN_U03
open Aeneas Aeneas.Std Result AspisR1TerminalDecoder

theorem conditional
    (encode : NFY_NBN_EncoderSummary.Encode) (decode : NFY_NBN_AfterDecodeTypes.Decode)
    (NBN_Dep_DigestEncodeCanonical : NFY_NBN_DigestResultDependency.NBN_Dep_DigestEncodeCanonical encode)
    (NBN_Dep_DigestDecode : NFY_NBN_AfterDecodeTypes.NBN_Dep_DigestDecode decode) :
    (∀ a, NFY_NBN_EncoderSummary.after encode a = pool_v1.pair_terminal.encode_pool_v1_pair_verified_afterstate_v1 a) ∧
    (∀ s out, NFY_NBN_EncoderSummary.live encode s out = pool_v1.pair_tree_profile.encode_pool_v1_pair_live_snapshot_v1 s out) ∧
    (∀ s out, NFY_NBN_LateSummary.run encode s out = pool_v1.pair_tree_profile.encode_pool_v1_pair_late_public_statement_v1 s out) ∧
    (∀ bytes, NFY_NBN_AfterstateDecoderDependency.run decode bytes = pool_v1.pair_terminal.decode_pool_v1_pair_verified_afterstate_v1 bytes) :=
  ⟨NFY_NBN_EncoderSummary.after_source encode NBN_Dep_DigestEncodeCanonical,
    NFY_NBN_EncoderSummary.live_source encode NBN_Dep_DigestEncodeCanonical,
    NFY_NBN_LateSummary.source encode NBN_Dep_DigestEncodeCanonical,
    NFY_NBN_AfterstateDecoderDependency.source decode NBN_Dep_DigestDecode⟩

#print axioms conditional
end NFY_NBN_U03
-- END copied NBN_U03
-- BEGIN copied NBN_U05: lean/NBN_U05.lean
set_option autoImplicit false
noncomputable section
namespace NFY_NBN_U05
open Aeneas Aeneas.Std Result AspisR1TerminalDecoder
open NFY_NBN_StatementResult NFY_NBN_ValidatorSummary

theorem conditional (enc : Encode) (t : Transfer → PaymentResult) (w : Withdrawal → PaymentResult)
    (NBN_Dep_DigestEncodeRaw : NFY_NBN_DigestResultDependency.NBN_Dep_DigestEncodeRaw enc)
    (NBN_Dep_TransferEncode : NFY_NBN_ValidatorSummary.NBN_Dep_TransferEncode t)
    (NBN_Dep_WithdrawalEncode : NFY_NBN_ValidatorSummary.NBN_Dep_WithdrawalEncode w) :
    (∀ s, NFY_NBN_ValidatorSummary.run enc t w s =
      pool_v1.pair_forest_terminal.validate_pool_v1_pair_forest_terminal_statement_v1 s) ∧
    (∀ s, NFY_NBN_StatementEncoderSummary.run enc t w s =
      NFY_NBN_StatementEncoderSummary.observe (AspisS6OuterNativeInstalled.encode s)) :=
  ⟨NFY_NBN_ValidatorSummary.source enc t w (fun d _ => NBN_Dep_DigestEncodeRaw d)
      NBN_Dep_TransferEncode NBN_Dep_WithdrawalEncode,
    NFY_NBN_StatementEncoderSummary.source enc t w NBN_Dep_DigestEncodeRaw
      NBN_Dep_TransferEncode NBN_Dep_WithdrawalEncode⟩

/-- The SAME fifth tuple component reaches the validator's output-lane child. -/
theorem validator_nullifier (s : Statement) :
    (parts s).2.2.2.2.1 = match s with
      | .PrivateTransfer _ p => p.nullifier
      | .Withdrawal _ p => p.nullifier := NBD_TerminalProjection.nullifier_same s

/-- The SAME variant selects the actual encoder prefix tag. -/
theorem encoder_kind (s : Statement) : NFY_NBN_EncoderBytes.tag s = match s with
    | .PrivateTransfer _ _ => 1#u8
    | .Withdrawal _ _ => 2#u8 := by cases s <;> rfl

#print axioms conditional
#print axioms validator_nullifier
#print axioms encoder_kind
end NFY_NBN_U05
-- END copied NBN_U05
-- BEGIN copied NBP_DigestEncode: lean/NBP_DigestEncode.lean
set_option autoImplicit false
noncomputable section
namespace NFY_NBP_DigestEncode
open Aeneas Aeneas.Std Result AspisR1TerminalDecoder
open AspisR1.S2K
/-- Exact full encoder, all raw limbs; reuses the existing decreasing-loop
induction on the selected cohort rather than re-proving it. -/
theorem result (digest : Array U32 8#usize) :
    atomic_statement.encode_digest_canonical digest = ok (DigestBytes.bytes digest) :=
  DigestBytes.exact digest
/-- The same arbitrary pre-state update checked by native NBG_K020. -/
theorem step (digest : Array U32 8#usize) (index : Usize)
    (range : index.val < 8) (output : Array U8 32#usize) :
    atomic_statement.encode_digest_canonical_loop.body (DigestTotal.cursor digest index) output =
      ok (.cont
        (DigestTotal.cursor digest (Usize.ofNatCore (index.val+1) (by scalar_tac)),
         output.setSlice! (4*index.val)
           (core.num.U32.to_le_bytes
             (digest.val[index.val]'(by have := digest.property; change digest.val.length=8 at this; omega))).val)) :=
  DigestTotal.body_word digest index range output
#print axioms result
#print axioms step
#print axioms DigestBytes.loop_exact
#print axioms DigestTotal.next_row
#print axioms DigestTotal.exhausted
end NFY_NBP_DigestEncode
-- END copied NBP_DigestEncode
-- BEGIN copied NBP_ArrayIndex: lean/NBP_ArrayIndex.lean
set_option autoImplicit false
namespace NFY_NBP_ArrayIndex
open Aeneas Aeneas.Std Result

def slice {N : Usize} (output : Array U8 N) (start stop : Usize) : Slice U8 :=
  ⟨output.val.slice start.val stop.val, by scalar_tac⟩

theorem index_mut {N : Usize} (output : Array U8 N) (start stop : Usize)
    (order : start.val ≤ stop.val) (bound : stop.val ≤ N.val) :
    core.array.Array.index_mut
      (core.ops.index.IndexMutSlice (core.slice.index.SliceIndexRangeUsizeSlice U8))
      output {start,«end»:=stop} =
    ok (slice output start stop,fun s => output.setSlice! start.val s.val) := by
  simp [core.array.Array.index_mut,core.ops.index.IndexMutSlice,
    core.slice.index.Slice.index_mut,core.slice.index.SliceIndexRangeUsizeSlice,
    core.slice.index.SliceIndexRangeUsizeSlice.index_mut,
    Array.to_slice,Slice.length,Slice.len,order,bound,output.property,
    Array.from_slice,Aeneas.Std.Array.setSlice!,slice]

theorem copy {W : Usize} (s : Slice U8) (bytes : Array U8 W)
    (width : s.length = W.val) :
    core.slice.Slice.copy_from_slice core.marker.CopyU8 s bytes.to_slice = ok bytes.to_slice := by
  simp [core.slice.Slice.copy_from_slice,Slice.len,Slice.length,
    Array.to_slice,bytes.property,width]
theorem slice_length {N : Usize} (output : Array U8 N) (start stop : Usize)
    (order : start.val ≤ stop.val) (bound : stop.val ≤ N.val) :
    (slice output start stop).length = stop.val-start.val := by
  simp only [slice,Slice.length,List.slice,List.length_take,List.length_drop,output.property]
  omega

theorem copy_range {N W : Usize} (output : Array U8 N) (start stop : Usize)
    (bytes : Array U8 W) (order : start.val ≤ stop.val) (bound : stop.val ≤ N.val)
    (width : stop.val-start.val = W.val) :
    core.slice.Slice.copy_from_slice core.marker.CopyU8 (slice output start stop) bytes.to_slice =
      ok bytes.to_slice :=
  copy _ bytes ((slice_length output start stop order bound).trans width)

theorem prefix_index {N : Usize} (output : Array U8 N) (stop : Usize) (bound : stop.val ≤ N.val) :
    core.array.Array.index_mut
      (core.ops.index.IndexMutSlice (core.slice.index.SliceIndexRangeToUsizeSlice U8))
      output {«end»:=stop} =
    ok (slice output 0#usize stop,fun s => output.setSlice! 0 s.val) := by
  simp [core.array.Array.index_mut,core.ops.index.IndexMutSlice,
    core.slice.index.Slice.index_mut,core.slice.index.SliceIndexRangeToUsizeSlice,
    core.slice.index.SliceIndexRangeToUsizeSlice.index_mut,
    Array.to_slice,Slice.length,Slice.len,bound,output.property,
    Array.from_slice,Aeneas.Std.Array.setSlice!,slice]

theorem suffix_index {N : Usize} (output : Array U8 N) (start : Usize) (bound : start.val ≤ N.val) :
    core.array.Array.index_mut
      (core.ops.index.IndexMutSlice (core.slice.index.SliceIndexRangeFromUsizeSlice U8))
      output {start} =
    ok (slice output start N,fun s => output.setSlice! start.val s.val) := by
  simp [core.array.Array.index_mut,core.ops.index.IndexMutSlice,
    core.slice.index.Slice.index_mut,core.slice.index.SliceIndexRangeFromUsizeSlice,
    core.slice.index.SliceIndexRangeFromUsizeSlice.index_mut,
    Array.to_slice,Slice.length,Slice.len,bound,output.property,
    Array.from_slice,Aeneas.Std.Array.setSlice!,slice,List.slice,List.take_length,List.length_drop]
  apply Subtype.ext
  change output.val.drop start.val = (output.val.drop start.val).take (N.val-start.val)
  have len : (output.val.drop start.val).length = N.val-start.val := by simp [output.property]
  rw [←len,List.take_length]
#print axioms suffix_index

#print axioms slice_length
#print axioms copy_range
#print axioms prefix_index
#print axioms index_mut
#print axioms copy
end NFY_NBP_ArrayIndex
-- END copied NBP_ArrayIndex
-- BEGIN copied NBP_Store: lean/NBP_Store.lean
set_option autoImplicit false
noncomputable section
namespace NFY_NBP_Store
open Aeneas Aeneas.Std Result WP

def store {N W : Usize} (output : Array U8 N) (start stop : Usize)
    (bytes : Array U8 W) : Result (Array U8 N) := do
  let (s,back) ← core.array.Array.index_mut
    (core.ops.index.IndexMutSlice (core.slice.index.SliceIndexRangeUsizeSlice U8))
    output {start,«end»:=stop}
  let src ← lift (Array.to_slice bytes)
  let copied ← core.slice.Slice.copy_from_slice core.marker.CopyU8 s src
  ok (back copied)

theorem exact {N W : Usize} (output : Array U8 N) (start stop : Usize)
    (bytes : Array U8 W) (order : start.val ≤ stop.val) (bound : stop.val ≤ N.val)
    (width : stop.val-start.val = W.val) :
    store output start stop bytes = ok (output.setSlice! start.val bytes.val) := by
  have room : W.val ≤ N.val-start.val := by omega
  simp only [store,core.array.Array.index_mut,core.ops.index.IndexMutSlice,
    core.slice.index.Slice.index_mut,core.slice.index.SliceIndexRangeUsizeSlice,
    core.slice.index.SliceIndexRangeUsizeSlice.index_mut,Array.to_slice]
  simp [Slice.length,Slice.len,order,bound,output.property,bytes.property,
    core.slice.Slice.copy_from_slice,List.slice,width,Nat.min_eq_left room,
    Array.from_slice,lift]
  rfl

theorem store_then {N W : Usize} {T : Type} (output : Array U8 N) (start stop : Usize)
    (bytes : Array U8 W) (k : Array U8 N → Result T)
    (order : start.val ≤ stop.val) (bound : stop.val ≤ N.val)
    (width : stop.val-start.val = W.val) :
    (do
      let (s,back) ← core.array.Array.index_mut
        (core.ops.index.IndexMutSlice (core.slice.index.SliceIndexRangeUsizeSlice U8))
        output {start,«end»:=stop}
      let src ← lift (Array.to_slice bytes)
      let copied ← core.slice.Slice.copy_from_slice core.marker.CopyU8 s src
      k (back copied)) = k (output.setSlice! start.val bytes.val) := by
  have h := congrArg (fun r => r >>= k) (exact output start stop bytes order bound width)
  cases indexed : core.array.Array.index_mut
      (core.ops.index.IndexMutSlice (core.slice.index.SliceIndexRangeUsizeSlice U8))
      output {start,«end»:=stop} with
  | fail e => simp only [store,indexed,bind_tc_fail] at h ⊢; exact h
  | div => simp only [store,indexed,bind_tc_div] at h ⊢; exact h
  | ok pair =>
    rcases pair with ⟨s,back⟩
    simp only [store,indexed,bind_tc_ok] at h ⊢
    change ((do
      let copied ← core.slice.Slice.copy_from_slice core.marker.CopyU8 s bytes.to_slice
      ok (back copied)) >>= k) = _ at h
    change (do
      let copied ← core.slice.Slice.copy_from_slice core.marker.CopyU8 s bytes.to_slice
      k (back copied)) = _
    cases copied : core.slice.Slice.copy_from_slice core.marker.CopyU8 s bytes.to_slice <;>
      simpa only [copied,bind_tc_ok,bind_tc_fail,bind_tc_div] using h
theorem update {N : Usize} (output : Array U8 N) (index : Usize) (value : U8)
    (bound : index.val < N.val) :
    output.update index value = ok (output.set index value) := by
  obtain ⟨out,call,same⟩ := spec_imp_exists
    (Array.update_spec output index value (by simpa only [Array.length,output.property] using bound))
  simpa only [same] using call
#print axioms update
#print axioms exact
#print axioms store_then
#print Array.update
#print Array.setSlice!
end NFY_NBP_Store
-- END copied NBP_Store
-- BEGIN copied NBP_CommonTail6: lean/NBP_CommonTail6.lean
set_option autoImplicit false
noncomputable section
namespace NFY_NBP_CommonTail6
open Aeneas Aeneas.Std Result AspisR1TerminalDecoder
abbrev C := pool_v1.payment_relation.CommonPublicV1
abbrev K := pool_v1.historical_anchor.PoolV1TransitionKind

def run (output : Array U8 216#usize) (common : C) : Result (Array U8 216#usize) := do
  let (s18, index_mut_back6) ← core.array.Array.index_mut (core.ops.index.IndexMutSlice (core.slice.index.SliceIndexRangeUsizeSlice Std.U8)) output { start := pool_v1.payment_relation.ASSET_ID_OFFSET, «end» := pool_v1.payment_relation.AMOUNT_OR_RESERVED_OFFSET }
  let a3 ← aspis_core.field.M31.to_le_bytes common.asset_id
  let s19 ← lift (Array.to_slice a3)
  let s20 ← core.slice.Slice.copy_from_slice core.marker.CopyU8 s18 s19
  ok (index_mut_back6 s20)
def expected (output : Array U8 216#usize) (common : C) : Array U8 216#usize :=
  output.setSlice! 144 (core.num.U32.to_le_bytes common.asset_id).val

theorem result (output : Array U8 216#usize) (common : C) : run output common = ok (expected output common) := by
  unfold run
  simp only [pool_v1.payment_relation.POOL_OFFSET,pool_v1.payment_relation.DEPLOYMENT_DOMAIN_OFFSET,
    pool_v1.payment_relation.ANCHOR_SEQUENCE_OFFSET,pool_v1.payment_relation.ANCHOR_ROOT_OFFSET,
    pool_v1.payment_relation.NULLIFIER_OFFSET,pool_v1.payment_relation.ASSET_ID_OFFSET,
    pool_v1.payment_relation.AMOUNT_OR_RESERVED_OFFSET,
    pool_v1.payment_relation.POOL_V1_PAYMENT_STATEMENT_VERSION,
    pool_v1.format.POOL_V1_DIGEST_ENCODING_VERSION,NFY_NBP_DigestEncode.result,NFY_NBG_Header.tag_result,
    aspis_core.field.M31.to_le_bytes,lift,bind_tc_ok]
  rw [NFY_NBP_ArrayIndex.index_mut output 144#usize 148#usize (by decide) (by decide)]
  change (do
    let copied ← core.slice.Slice.copy_from_slice core.marker.CopyU8
      (NFY_NBP_ArrayIndex.slice output 144#usize 148#usize) (core.num.U32.to_le_bytes common.asset_id).to_slice
    _) = _
  rw [NFY_NBP_ArrayIndex.copy_range output 144#usize 148#usize (core.num.U32.to_le_bytes common.asset_id) (by decide) (by decide) (by decide)]
  simp only [bind_tc_ok]
  rfl
#print axioms result
end NFY_NBP_CommonTail6
-- END copied NBP_CommonTail6
-- BEGIN copied NBP_CommonTail5: lean/NBP_CommonTail5.lean
set_option autoImplicit false
noncomputable section
namespace NFY_NBP_CommonTail5
open Aeneas Aeneas.Std Result AspisR1TerminalDecoder
abbrev C := pool_v1.payment_relation.CommonPublicV1
abbrev K := pool_v1.historical_anchor.PoolV1TransitionKind

def run (output : Array U8 216#usize) (common : C) : Result (Array U8 216#usize) := do
  let (s15, index_mut_back5) ← core.array.Array.index_mut (core.ops.index.IndexMutSlice (core.slice.index.SliceIndexRangeUsizeSlice Std.U8)) output { start := pool_v1.payment_relation.NULLIFIER_OFFSET, «end» := pool_v1.payment_relation.ASSET_ID_OFFSET }
  let a2 ← atomic_statement.encode_digest_canonical common.nullifier
  let s16 ← lift (Array.to_slice a2)
  let s17 ← core.slice.Slice.copy_from_slice core.marker.CopyU8 s15 s16
  let output9 := index_mut_back5 s17
  NFY_NBP_CommonTail6.run output9 common

def expected (output : Array U8 216#usize) (common : C) : Array U8 216#usize :=
  NFY_NBP_CommonTail6.expected (output.setSlice! 112 (AspisR1.S2K.DigestBytes.bytes common.nullifier).val) common

theorem result (output : Array U8 216#usize) (common : C) : run output common = ok (expected output common) := by
  unfold run
  simp only [pool_v1.payment_relation.POOL_OFFSET,pool_v1.payment_relation.DEPLOYMENT_DOMAIN_OFFSET,
    pool_v1.payment_relation.ANCHOR_SEQUENCE_OFFSET,pool_v1.payment_relation.ANCHOR_ROOT_OFFSET,
    pool_v1.payment_relation.NULLIFIER_OFFSET,pool_v1.payment_relation.ASSET_ID_OFFSET,
    pool_v1.payment_relation.AMOUNT_OR_RESERVED_OFFSET,
    pool_v1.payment_relation.POOL_V1_PAYMENT_STATEMENT_VERSION,
    pool_v1.format.POOL_V1_DIGEST_ENCODING_VERSION,NFY_NBP_DigestEncode.result,NFY_NBG_Header.tag_result,
    aspis_core.field.M31.to_le_bytes,lift,bind_tc_ok]
  rw [NFY_NBP_ArrayIndex.index_mut output 112#usize 144#usize (by decide) (by decide)]
  change (do
    let copied ← core.slice.Slice.copy_from_slice core.marker.CopyU8
      (NFY_NBP_ArrayIndex.slice output 112#usize 144#usize) (AspisR1.S2K.DigestBytes.bytes common.nullifier).to_slice
    _) = _
  rw [NFY_NBP_ArrayIndex.copy_range output 112#usize 144#usize (AspisR1.S2K.DigestBytes.bytes common.nullifier) (by decide) (by decide) (by decide)]
  simp only [bind_tc_ok]
  rw [NFY_NBP_CommonTail6.result]
  rfl
#print axioms result
end NFY_NBP_CommonTail5
-- END copied NBP_CommonTail5
-- BEGIN copied NBP_CommonTail4: lean/NBP_CommonTail4.lean
set_option autoImplicit false
noncomputable section
namespace NFY_NBP_CommonTail4
open Aeneas Aeneas.Std Result AspisR1TerminalDecoder
abbrev C := pool_v1.payment_relation.CommonPublicV1
abbrev K := pool_v1.historical_anchor.PoolV1TransitionKind

def run (output : Array U8 216#usize) (common : C) : Result (Array U8 216#usize) := do
  let (s12, index_mut_back4) ← core.array.Array.index_mut (core.ops.index.IndexMutSlice (core.slice.index.SliceIndexRangeUsizeSlice Std.U8)) output { start := pool_v1.payment_relation.ANCHOR_ROOT_OFFSET, «end» := pool_v1.payment_relation.NULLIFIER_OFFSET }
  let a1 ← atomic_statement.encode_digest_canonical common.anchor_root
  let s13 ← lift (Array.to_slice a1)
  let s14 ← core.slice.Slice.copy_from_slice core.marker.CopyU8 s12 s13
  let output8 := index_mut_back4 s14
  NFY_NBP_CommonTail5.run output8 common

def expected (output : Array U8 216#usize) (common : C) : Array U8 216#usize :=
  NFY_NBP_CommonTail5.expected (output.setSlice! 80 (AspisR1.S2K.DigestBytes.bytes common.anchor_root).val) common

theorem result (output : Array U8 216#usize) (common : C) : run output common = ok (expected output common) := by
  unfold run
  simp only [pool_v1.payment_relation.POOL_OFFSET,pool_v1.payment_relation.DEPLOYMENT_DOMAIN_OFFSET,
    pool_v1.payment_relation.ANCHOR_SEQUENCE_OFFSET,pool_v1.payment_relation.ANCHOR_ROOT_OFFSET,
    pool_v1.payment_relation.NULLIFIER_OFFSET,pool_v1.payment_relation.ASSET_ID_OFFSET,
    pool_v1.payment_relation.AMOUNT_OR_RESERVED_OFFSET,
    pool_v1.payment_relation.POOL_V1_PAYMENT_STATEMENT_VERSION,
    pool_v1.format.POOL_V1_DIGEST_ENCODING_VERSION,NFY_NBP_DigestEncode.result,NFY_NBG_Header.tag_result,
    aspis_core.field.M31.to_le_bytes,lift,bind_tc_ok]
  rw [NFY_NBP_ArrayIndex.index_mut output 80#usize 112#usize (by decide) (by decide)]
  change (do
    let copied ← core.slice.Slice.copy_from_slice core.marker.CopyU8
      (NFY_NBP_ArrayIndex.slice output 80#usize 112#usize) (AspisR1.S2K.DigestBytes.bytes common.anchor_root).to_slice
    _) = _
  rw [NFY_NBP_ArrayIndex.copy_range output 80#usize 112#usize (AspisR1.S2K.DigestBytes.bytes common.anchor_root) (by decide) (by decide) (by decide)]
  simp only [bind_tc_ok]
  rw [NFY_NBP_CommonTail5.result]
  rfl
#print axioms result
end NFY_NBP_CommonTail4
-- END copied NBP_CommonTail4
-- BEGIN copied NBP_CommonTail3: lean/NBP_CommonTail3.lean
set_option autoImplicit false
noncomputable section
namespace NFY_NBP_CommonTail3
open Aeneas Aeneas.Std Result AspisR1TerminalDecoder
abbrev C := pool_v1.payment_relation.CommonPublicV1
abbrev K := pool_v1.historical_anchor.PoolV1TransitionKind

def run (output : Array U8 216#usize) (common : C) : Result (Array U8 216#usize) := do
  let (s9, index_mut_back3) ← core.array.Array.index_mut (core.ops.index.IndexMutSlice (core.slice.index.SliceIndexRangeUsizeSlice Std.U8)) output { start := pool_v1.payment_relation.ANCHOR_SEQUENCE_OFFSET, «end» := pool_v1.payment_relation.ANCHOR_ROOT_OFFSET }
  let a ← lift (core.num.U64.to_le_bytes common.anchor_sequence)
  let s10 ← lift (Array.to_slice a)
  let s11 ← core.slice.Slice.copy_from_slice core.marker.CopyU8 s9 s10
  let output7 := index_mut_back3 s11
  NFY_NBP_CommonTail4.run output7 common

def expected (output : Array U8 216#usize) (common : C) : Array U8 216#usize :=
  NFY_NBP_CommonTail4.expected (output.setSlice! 72 (core.num.U64.to_le_bytes common.anchor_sequence).val) common

theorem result (output : Array U8 216#usize) (common : C) : run output common = ok (expected output common) := by
  unfold run
  simp only [pool_v1.payment_relation.POOL_OFFSET,pool_v1.payment_relation.DEPLOYMENT_DOMAIN_OFFSET,
    pool_v1.payment_relation.ANCHOR_SEQUENCE_OFFSET,pool_v1.payment_relation.ANCHOR_ROOT_OFFSET,
    pool_v1.payment_relation.NULLIFIER_OFFSET,pool_v1.payment_relation.ASSET_ID_OFFSET,
    pool_v1.payment_relation.AMOUNT_OR_RESERVED_OFFSET,
    pool_v1.payment_relation.POOL_V1_PAYMENT_STATEMENT_VERSION,
    pool_v1.format.POOL_V1_DIGEST_ENCODING_VERSION,NFY_NBP_DigestEncode.result,NFY_NBG_Header.tag_result,
    aspis_core.field.M31.to_le_bytes,lift,bind_tc_ok]
  rw [NFY_NBP_ArrayIndex.index_mut output 72#usize 80#usize (by decide) (by decide)]
  change (do
    let copied ← core.slice.Slice.copy_from_slice core.marker.CopyU8
      (NFY_NBP_ArrayIndex.slice output 72#usize 80#usize) (core.num.U64.to_le_bytes common.anchor_sequence).to_slice
    _) = _
  rw [NFY_NBP_ArrayIndex.copy_range output 72#usize 80#usize (core.num.U64.to_le_bytes common.anchor_sequence) (by decide) (by decide) (by decide)]
  simp only [bind_tc_ok]
  rw [NFY_NBP_CommonTail4.result]
  rfl
#print axioms result
end NFY_NBP_CommonTail3
-- END copied NBP_CommonTail3
-- BEGIN copied NBP_CommonTail2: lean/NBP_CommonTail2.lean
set_option autoImplicit false
noncomputable section
namespace NFY_NBP_CommonTail2
open Aeneas Aeneas.Std Result AspisR1TerminalDecoder
abbrev C := pool_v1.payment_relation.CommonPublicV1
abbrev K := pool_v1.historical_anchor.PoolV1TransitionKind

def run (output : Array U8 216#usize) (common : C) : Result (Array U8 216#usize) := do
  let (s6, index_mut_back2) ← core.array.Array.index_mut (core.ops.index.IndexMutSlice (core.slice.index.SliceIndexRangeUsizeSlice Std.U8)) output { start := pool_v1.payment_relation.DEPLOYMENT_DOMAIN_OFFSET, «end» := pool_v1.payment_relation.ANCHOR_SEQUENCE_OFFSET }
  let s7 ← lift (Array.to_slice common.deployment_domain)
  let s8 ← core.slice.Slice.copy_from_slice core.marker.CopyU8 s6 s7
  let output6 := index_mut_back2 s8
  NFY_NBP_CommonTail3.run output6 common

def expected (output : Array U8 216#usize) (common : C) : Array U8 216#usize :=
  NFY_NBP_CommonTail3.expected (output.setSlice! 40 common.deployment_domain.val) common

theorem result (output : Array U8 216#usize) (common : C) : run output common = ok (expected output common) := by
  unfold run
  simp only [pool_v1.payment_relation.POOL_OFFSET,pool_v1.payment_relation.DEPLOYMENT_DOMAIN_OFFSET,
    pool_v1.payment_relation.ANCHOR_SEQUENCE_OFFSET,pool_v1.payment_relation.ANCHOR_ROOT_OFFSET,
    pool_v1.payment_relation.NULLIFIER_OFFSET,pool_v1.payment_relation.ASSET_ID_OFFSET,
    pool_v1.payment_relation.AMOUNT_OR_RESERVED_OFFSET,
    pool_v1.payment_relation.POOL_V1_PAYMENT_STATEMENT_VERSION,
    pool_v1.format.POOL_V1_DIGEST_ENCODING_VERSION,NFY_NBP_DigestEncode.result,NFY_NBG_Header.tag_result,
    aspis_core.field.M31.to_le_bytes,lift,bind_tc_ok]
  rw [NFY_NBP_ArrayIndex.index_mut output 40#usize 72#usize (by decide) (by decide)]
  change (do
    let copied ← core.slice.Slice.copy_from_slice core.marker.CopyU8
      (NFY_NBP_ArrayIndex.slice output 40#usize 72#usize) common.deployment_domain.to_slice
    _) = _
  rw [NFY_NBP_ArrayIndex.copy_range output 40#usize 72#usize common.deployment_domain (by decide) (by decide) (by decide)]
  simp only [bind_tc_ok]
  rw [NFY_NBP_CommonTail3.result]
  rfl
#print axioms result
end NFY_NBP_CommonTail2
-- END copied NBP_CommonTail2

run_cmd do
 let env ← Lean.getEnv
 env.constants.toList.forM fun (n, ci) => do
  if ci.isTheorem && (env.getModuleIdxFor? n).isNone then
   Lean.Elab.Command.elabCommand (← `(command| #print axioms $(Lean.mkIdent n)))
