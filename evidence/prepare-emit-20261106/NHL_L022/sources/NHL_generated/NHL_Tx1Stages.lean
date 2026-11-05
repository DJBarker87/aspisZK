import NHL_Tx1Eq
import NHL_BindOn
set_option autoImplicit false
noncomputable section
namespace AspisR1.NHL_Tx1Stages
open Aeneas Aeneas.Std Result AspisR1CurrentCaller
abbrev Out := core.result.Result (alloc.vec.Vec U8) verifier.Error
structure Context where
 prepared : verifier.Prepared
 accumulator : verifier.Accumulator
 scratch : Array aspis_core.field.wide_exact.WideExact 29#usize
 geometry : verifier.QueryGeometry
 pending : verifier.BatchedWeights

def beforeQuery (ops : Ops) {H : Type} (prepareCall : NHL_EmittedTx1.Prepare H)
 (aspis_coredigestDigest32Inst : aspis_core.digest.Digest32 H)
 (public1 : aspis_statement.pool_v1.pair_forest_semantic_terminal.r0.Public)
 (public_bytes proof : Slice U8) (k : Usize) (hash : H)
 (obs : Option (verifier.Phase → Result Unit)) : Result (core.result.Result Context verifier.Error)
  := do
  if k != compact.SPLIT
  then ok (core.result.Result.Err verifier.Error.Parse)
  else
    let r ← ops.op3 proof
    let cf ← core.result.Result.Insts.CoreOpsTry.branch r
    match cf with
    | core.ops.control_flow.ControlFlow.Continue _ =>
      let r1 ← ops.op4 proof
      let cf1 ← core.result.Result.Insts.CoreOpsTry.branch r1
      match cf1 with
      | core.ops.control_flow.ControlFlow.Continue _ =>
        verifier.mark obs verifier.Phase.Parsed
        let we ← (AspisR1CurrentCaller.aspis_core.field.wide_exact.WideExact.ZERO ops)
        let g := Array.repeat 29#usize we
        let (r2, g1) ←
          prepareCall aspis_coredigestDigest32Inst public1 proof
            hash obs g
        let cf2 ← core.result.Result.Insts.CoreOpsTry.branch r2
        match cf2 with
        | core.ops.control_flow.ControlFlow.Continue val =>
          let r3 ← ops.op20 transport.Variant.S2
          let cf3 ← core.result.Result.Insts.CoreOpsTry.branch r3
          match cf3 with
          | core.ops.control_flow.ControlFlow.Continue val1 =>
            verifier.mark obs verifier.Phase.Prepare
            let i ← (AspisR1CurrentCaller.compact.OFF_FOLDED_ROOT ops)
            let i1 ← (AspisR1CurrentCaller.compact.OFF_ROUND1 ops)
            let s ←
              core.slice.index.Slice.index
                (core.slice.index.SliceIndexRangeUsizeSlice Std.U8) proof
                { start := i, «end» := i1 }
            let r4 ←
              core.array.TryFromArrayCopySlice.try_from 32#usize
                core.marker.CopyU8 s
            let folded_root ←
              core.result.Result.unwrap core.fmt.DebugTryFromSliceError r4
            let r5 ←
              ops.op6 aspis_coredigestDigest32Inst
                proof val folded_root 0#usize hash
            let cf4 ← core.result.Result.Insts.CoreOpsTry.branch r5
            match cf4 with
            | core.ops.control_flow.ControlFlow.Continue _ =>
              verifier.mark obs (verifier.Phase.Merkle 0#usize)
              let r6 ← ops.op19 val.queries 0#usize k
              let cf5 ← core.result.Result.Insts.CoreOpsTry.branch r6
              match cf5 with
              | core.ops.control_flow.ControlFlow.Continue val2 =>
                let s1 := alloc.vec.Vec.deref val1.weights
                let r7 ← ops.op18 s1
                let cf6 ← core.result.Result.Insts.CoreOpsTry.branch r7
                match cf6 with
                | core.ops.control_flow.ControlFlow.Continue val3 =>
                  ok (.Ok ⟨val,val1,g1,val2,val3⟩)
                | core.ops.control_flow.ControlFlow.Break residual =>
                  core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
                    Context (core.convert.FromSame
                    verifier.Error) residual
              | core.ops.control_flow.ControlFlow.Break residual =>
                core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
                  Context (core.convert.FromSame verifier.Error)
                  residual
            | core.ops.control_flow.ControlFlow.Break residual =>
              core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
                Context (core.convert.FromSame verifier.Error)
                residual
          | core.ops.control_flow.ControlFlow.Break residual =>
            core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
              Context (core.convert.FromSame verifier.Error)
              residual
        | core.ops.control_flow.ControlFlow.Break residual =>
          core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
            Context (core.convert.FromSame verifier.Error)
            residual
      | core.ops.control_flow.ControlFlow.Break residual =>
        core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
          Context (core.convert.FromSame verifier.Error)
          residual
    | core.ops.control_flow.ControlFlow.Break residual =>
      core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
        Context (core.convert.FromSame verifier.Error) residual

def afterQuery (ops : Ops) {H : Type} (D : aspis_core.digest.Digest32 H)
 (public_bytes proof : Slice U8) (hash : H) (obs : Option (verifier.Phase → Result Unit))
 (p : verifier.Prepared) (a : verifier.Accumulator) (pending : verifier.BatchedWeights) : Result Out := do
 let (s,back) ← lift (alloc.vec.Vec.deref_mut a.weights)
 let s1 ← ops.op17 pending s
 let bytes ← ops.op16 D p {a with weights:=back s1} proof public_bytes hash
 verifier.mark obs verifier.Phase.CheckpointWrite
 ok (.Ok bytes)

def queryCut (ops : Ops) {H : Type} (D : aspis_core.digest.Digest32 H)
 (public_bytes proof : Slice U8) (k : Usize) (hash : H)
 (obs : Option (verifier.Phase → Result Unit)) (c : Context) : Result Out := do
 let r ← ops.op7 proof c.prepared c.accumulator c.scratch obs c.geometry c.pending k
 let cf ← core.result.Result.Insts.CoreOpsTry.branch r
 match cf with
 | .Continue pair => afterQuery ops D public_bytes proof hash obs c.prepared pair.1 pair.2
 | .Break residual =>
   core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
     (alloc.vec.Vec U8) (core.convert.FromSame verifier.Error) residual

def run (ops : Ops) {H : Type} (prepareCall : NHL_EmittedTx1.Prepare H)
 (D : aspis_core.digest.Digest32 H)
 (pub : aspis_statement.pool_v1.pair_forest_semantic_terminal.r0.Public)
 (public_bytes proof : Slice U8) (k : Usize) (hash : H)
 (obs : Option (verifier.Phase → Result Unit)) : Result Out := do
 let r ← beforeQuery ops prepareCall D pub public_bytes proof k hash obs
 let cf ← core.result.Result.Insts.CoreOpsTry.branch r
 match cf with
 | .Continue c => queryCut ops D public_bytes proof k hash obs c
 | .Break residual =>
   core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
     (alloc.vec.Vec U8) (core.convert.FromSame verifier.Error) residual

theorem factor (ops : Ops) {H : Type} (prepareCall : NHL_EmittedTx1.Prepare H)
 (D : aspis_core.digest.Digest32 H)
 (pub : aspis_statement.pool_v1.pair_forest_semantic_terminal.r0.Public)
 (public_bytes proof : Slice U8) (k : Usize) (hash : H)
 (obs : Option (verifier.Phase → Result Unit)) :
 NHL_EmittedTx1.tx1 ops prepareCall D pub public_bytes proof k hash obs=
 run ops prepareCall D pub public_bytes proof k hash obs := by
 unfold NHL_EmittedTx1.tx1 run beforeQuery queryCut afterQuery
 simp only [bind_assoc_eq]
 repeat' first
 | rfl
 | (apply NFW_Bind.same; intro x)
 | (split <;> simp only [bind_tc_ok,bind_assoc_eq,Aeneas.Std.uncurry,
     core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,
     core.convert.FromSame])
 all_goals
   rename_i residual
   cases residual with
   | Ok impossible => cases impossible
   | Err error => rfl
#print axioms factor
end AspisR1.NHL_Tx1Stages
