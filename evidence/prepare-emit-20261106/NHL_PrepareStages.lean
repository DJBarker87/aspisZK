import NHL_PrepareEq
import NHL_BindOn
set_option autoImplicit false
noncomputable section
namespace AspisR1.NHL_PrepareStages
open Aeneas Aeneas.Std Result AspisR1CurrentCaller
abbrev Scratch := Array aspis_core.field.wide_exact.WideExact 29#usize
abbrev Out := core.result.Result verifier.Prepared verifier.Error × Scratch

def buffers (ops : Ops) {H : Type} (aspis_coredigestDigest32Inst : aspis_core.digest.Digest32 H)
 (proof : Slice U8) : Result (core.result.Result verifier.View verifier.Error)
  := do
  let i ← (AspisR1CurrentCaller.compact.LOGICAL_SEMANTIC ops)
  let i1 ← AspisR1CurrentCaller.compact.LOGICAL_Y1
  let i2 ← lift (Std.Usize.wrapping_add i i1)
  let r ← ops.op1 core.marker.CopyU8 i2 0#u8
  let r1 ←
    AspisR1CurrentCaller.core.result.Result.map_err
      (verifier.candidate.prepare.closure.Insts.CoreOpsFunctionFnOnceTupleErrorError
      aspis_coredigestDigest32Inst) r ()
  let cf ← core.result.Result.Insts.CoreOpsTry.branch r1
  match cf with
  | core.ops.control_flow.ControlFlow.Continue val =>
    let (s, deref_mut_back) ← lift (alloc.vec.Vec.deref_mut val)
    let ((semantic, y1), split_at_mut_back) ←
      core.slice.Slice.split_at_mut s i
    let i3 ← (AspisR1CurrentCaller.compact.OFF_Y1 ops)
    let s1 ←
      core.slice.index.Slice.index (core.slice.index.SliceIndexRangeUsizeSlice
        Std.U8) proof { start := 16#usize, «end» := i3 }
    let (r2, semantic1) ← ops.op10 s1 semantic
    let cf1 ← core.result.Result.Insts.CoreOpsTry.branch r2
    match cf1 with
    | core.ops.control_flow.ControlFlow.Continue _ =>
      let i4 ← (AspisR1CurrentCaller.compact.OFF_INACTIVE ops)
      let s2 ←
        core.slice.index.Slice.index
          (core.slice.index.SliceIndexRangeUsizeSlice Std.U8) proof
          { start := i3, «end» := i4 }
      let (r3, y11) ← ops.op11 s2 y1
      let cf2 ← core.result.Result.Insts.CoreOpsTry.branch r3
      match cf2 with
      | core.ops.control_flow.ControlFlow.Continue _ =>
        let s3 := split_at_mut_back (semantic1, y11)
        let val1 := deref_mut_back s3
        let s4 ←
          alloc.vec.Vec.index (core.slice.index.SliceIndexRangeToUsizeSlice
            Std.U8) val1 { «end» := i }
        let s5 ←
          alloc.vec.Vec.index (core.slice.index.SliceIndexRangeFromUsizeSlice
            Std.U8) val1 { start := i }
        let r4 ← ops.op5 proof s4 s5
        ok r4
      | core.ops.control_flow.ControlFlow.Break residual =>
        let r4 ←
          core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
            verifier.View (AspisR1CurrentCaller.verifier.Error.Insts.CoreConvertFromCodecError ops)
            residual
        ok r4
    | core.ops.control_flow.ControlFlow.Break residual =>
      let r3 ←
        core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
          verifier.View (AspisR1CurrentCaller.verifier.Error.Insts.CoreConvertFromCodecError ops)
          residual
      ok r3
  | core.ops.control_flow.ControlFlow.Break residual =>
    let r2 ←
      core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
        verifier.View (core.convert.FromSame verifier.Error) residual
    ok r2

def semanticCut (ops : Ops) {H : Type} (D : aspis_core.digest.Digest32 H)
 (pub : aspis_statement.pool_v1.pair_forest_semantic_terminal.r0.Public)
 (hash : H) (obs : Option (verifier.Phase → Result Unit)) (g : Scratch)
 (v : verifier.View) : Result Out := do
 let r5 ← ops.op9 D pub v.semantic hash obs
 let r6 ← AspisR1CurrentCaller.core.result.Result.map_err
   (verifier.candidate.prepare.closure_1.Insts.CoreOpsFunctionFnOnceTupleErrorError D) r5 ()
 let cf ← core.result.Result.Insts.CoreOpsTry.branch r6
 match cf with
 | .Continue sem => do
   verifier.mark obs verifier.Phase.Semantic
   ops.op8 D sem v hash g
 | .Break residual => do
   let r ← core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
     verifier.Prepared (core.convert.FromSame verifier.Error) residual
   ok (r,g)

def run (ops : Ops) {H : Type} (D : aspis_core.digest.Digest32 H)
 (pub : aspis_statement.pool_v1.pair_forest_semantic_terminal.r0.Public)
 (proof : Slice U8) (hash : H) (obs : Option (verifier.Phase → Result Unit)) (g : Scratch) : Result Out := do
 let r ← buffers ops D proof
 let cf ← core.result.Result.Insts.CoreOpsTry.branch r
 match cf with
 | .Continue v => semanticCut ops D pub hash obs g v
 | .Break residual => do
   let r ← core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
     verifier.Prepared (core.convert.FromSame verifier.Error) residual
   ok (r,g)

theorem factor (ops : Ops) {H : Type} (D : aspis_core.digest.Digest32 H)
 (pub : aspis_statement.pool_v1.pair_forest_semantic_terminal.r0.Public)
 (proof : Slice U8) (hash : H) (obs : Option (verifier.Phase → Result Unit)) (g : Scratch) :
 NHL_EmittedPrepare.prepare ops D pub proof hash obs g=run ops D pub proof hash obs g := by
 unfold NHL_EmittedPrepare.prepare run buffers semanticCut
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
   | Err error =>
     simp only [bind_tc_ok,bind_assoc_eq,
       core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,
       core.result.Result.Insts.CoreOpsTry.branch,core.convert.FromSame]
     repeat' (apply NFW_Bind.same; intro x)
     rfl
#print axioms factor
end AspisR1.NHL_PrepareStages
