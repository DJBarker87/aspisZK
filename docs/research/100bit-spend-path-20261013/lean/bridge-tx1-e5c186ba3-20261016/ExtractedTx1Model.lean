import ExtractedPreparedModel
open Aeneas Aeneas.Std Result ControlFlow Error
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 2048
namespace AspisR1PublicPreparation
structure Tx1Model.Boundaries where
  filled : core.marker.Copy aspis_core.field.QM31 → Usize → aspis_core.field.QM31 →
    Result (core.result.Result (alloc.vec.Vec aspis_core.field.QM31) aspis_core.r0.Error)
  verify : {H : Type} → aspis_core.Digest32 H → pool_v1.pair_forest_semantic_terminal.r0.Public →
    Slice U8 → H → Option (verifier.Phase → Result Unit) →
    Result (core.result.Result (r1_semantic.Verified H) r1_wire.Error)
  powers : (N : Usize) → aspis_core.field.WideExact → Result (Array aspis_core.field.WideExact N)
  view : Slice U8 → Result (core.result.Result verifier.View verifier.Error)
  finish : {H : Type} → aspis_core.Digest32 H → verifier.View → verifier.Prepared →
    verifier.Accumulator → Array aspis_core.field.WideExact 29#usize → Slice U8 → Slice U8 →
    Usize → H → Option (verifier.Phase → Result Unit) →
    Result (core.result.Result (alloc.vec.Vec U8) verifier.Error)

@[global_simps, irreducible]
def Tx1Model.one : aspis_core.field.QM31 :=
  { c0 := { a := 1#u32, b := 0#u32 }, c1 := { a := 0#u32, b := 0#u32 } }

def Tx1Model.cloneQm
  (self : aspis_core.field.QM31) : Result aspis_core.field.QM31 := do
  ok self

@[reducible]
def Tx1Model.cloneInst : core.clone.Clone
  aspis_core.field.QM31 := {
  clone := Tx1Model.cloneQm
}

@[reducible]
def Tx1Model.copyInst : core.marker.Copy
  aspis_core.field.QM31 := {
  cloneInst := Tx1Model.cloneInst
}

def Tx1Model.final_len
  (self : transport.Variant) : Result Std.Usize := do
  let i ← transport.Variant.folds self
  let i1 ← 2#usize * i
  1024#usize >>> i1

def
  Tx1Model.allocationError
  (c : verifier.Accumulator.new.closure) (tupled_args : aspis_core.r0.Error) :
  Result verifier.Error
  := do
  ok verifier.Error.Allocation

@[reducible]
def Tx1Model.allocationErrorClosure
  : core.ops.function.FnOnce verifier.Accumulator.new.closure
  aspis_core.r0.Error verifier.Error := {
  call_once :=
    Tx1Model.allocationError
}

def Tx1Model.newAccumulator (B : Tx1Model.Boundaries)
  (v : transport.Variant) :
  Result (core.result.Result verifier.Accumulator verifier.Error)
  := do
  let i ← Tx1Model.final_len v
  let r ←
    B.filled Tx1Model.copyInst i
      aspis_core.field.QM31.ZERO
  let r1 ←
    core.result.Result.map_err
      Tx1Model.allocationErrorClosure
      r ()
  let cf ← core.result.Result.Insts.CoreOpsTry.branch r1
  match cf with
  | core.ops.control_flow.ControlFlow.Continue val =>
    ok (core.result.Result.Ok
      {
        weights := val,
        rhs := aspis_core.field.WideExact.ZERO,
        power := Tx1Model.one,
        next := 0#usize
      })
  | core.ops.control_flow.ControlFlow.Break residual =>
    core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
      verifier.Accumulator (core.convert.FromSame verifier.Error) residual

def Tx1Model.mark
  (obs : Option (verifier.Phase → Result Unit)) (p : verifier.Phase) :
  Result Unit
  := do
  match obs with
  | none => ok ()
  | some f => f p

def Tx1Model.semanticError
  {H : Type} (aspis_coreDigest32Inst : aspis_core.Digest32 H)
  (c : verifier.tx1.closure H) (tupled_args : r1_wire.Error) :
  Result verifier.Error
  := do
  ok verifier.Error.Semantic

@[reducible]
def Tx1Model.semanticErrorClosure {H : Type}
  (aspis_coreDigest32Inst : aspis_core.Digest32 H) : core.ops.function.FnOnce
  (verifier.tx1.closure H) r1_wire.Error verifier.Error := {
  call_once :=
    Tx1Model.semanticError
    aspis_coreDigest32Inst
}

def Tx1Model.tx1 (B : Tx1Model.Boundaries) (P : PreparedModel.Boundaries)
  {H : Type} (aspis_coreDigest32Inst : aspis_core.Digest32 H)
  (public1 : pool_v1.pair_forest_semantic_terminal.r0.Public)
  (public_bytes : Slice Std.U8) (proof : Slice Std.U8) (k : Std.Usize)
  (hash : H) (obs : Option (verifier.Phase → Result Unit)) :
  Result (core.result.Result (alloc.vec.Vec Std.U8) verifier.Error)
  := do
  if k > 22#usize
  then ok (core.result.Result.Err verifier.Error.Parse)
  else
    let r ← B.view proof
    let cf ← core.result.Result.Insts.CoreOpsTry.branch r
    match cf with
    | core.ops.control_flow.ControlFlow.Continue v =>
      Tx1Model.mark obs verifier.Phase.Parsed
      let r1 ←
        B.verify aspis_coreDigest32Inst public1 v.semantic
          hash obs
      let r2 ←
        core.result.Result.map_err
          (Tx1Model.semanticErrorClosure
          aspis_coreDigest32Inst) r1 ()
      let cf1 ← core.result.Result.Insts.CoreOpsTry.branch r2
      match cf1 with
      | core.ops.control_flow.ControlFlow.Continue val =>
        Tx1Model.mark obs verifier.Phase.Semantic
        let r3 ← PreparedModel.prepare P aspis_coreDigest32Inst val v hash
        let cf2 ← core.result.Result.Insts.CoreOpsTry.branch r3
        match cf2 with
        | core.ops.control_flow.ControlFlow.Continue val1 =>
          let r4 ← Tx1Model.newAccumulator B v.variant
          let cf3 ← core.result.Result.Insts.CoreOpsTry.branch r4
          match cf3 with
          | core.ops.control_flow.ControlFlow.Continue val2 =>
            let g ← B.powers 29#usize val1.gamma
            Tx1Model.mark obs verifier.Phase.Prepare
            B.finish aspis_coreDigest32Inst v val1 val2 g
              public_bytes proof k hash obs
          | core.ops.control_flow.ControlFlow.Break residual =>
            core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
              (alloc.vec.Vec Std.U8) (core.convert.FromSame verifier.Error)
              residual
        | core.ops.control_flow.ControlFlow.Break residual =>
          core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
            (alloc.vec.Vec Std.U8) (core.convert.FromSame verifier.Error)
            residual
      | core.ops.control_flow.ControlFlow.Break residual =>
        core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
          (alloc.vec.Vec Std.U8) (core.convert.FromSame verifier.Error)
          residual
    | core.ops.control_flow.ControlFlow.Break residual =>
      core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
        (alloc.vec.Vec Std.U8) (core.convert.FromSame verifier.Error) residual

#print axioms Tx1Model.one
#print axioms Tx1Model.cloneQm
#print axioms Tx1Model.cloneInst
#print axioms Tx1Model.copyInst
#print axioms Tx1Model.final_len
#print axioms Tx1Model.allocationError
#print axioms Tx1Model.allocationErrorClosure
#print axioms Tx1Model.newAccumulator
#print axioms Tx1Model.mark
#print axioms Tx1Model.semanticError
#print axioms Tx1Model.semanticErrorClosure
#print axioms Tx1Model.tx1
end AspisR1PublicPreparation
