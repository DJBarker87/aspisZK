import ExtractedSemanticRoundsModel
import S1SemanticPrefixModelV1
open Aeneas Aeneas.Std Result ControlFlow Error
set_option autoImplicit false
namespace AspisR1PublicPreparation
inductive FinishModel.CircleRow where
| First : FinishModel.CircleRow
| Second : FinishModel.CircleRow

def FinishModel.CircleRow.read_discriminant : FinishModel.CircleRow → Isize
  | .First => 0#isize
  | .Second => 1#isize
instance _root_.AspisR1PublicPreparation.FinishModel.CircleRow.instDiscriminant :
    Aeneas.Std.Discriminant FinishModel.CircleRow Isize where
  read_discriminant := FinishModel.CircleRow.read_discriminant

@[reducible]
def FinishModel.Closure2 (H : Type) :=
  Array (Array aspis_core.field.QM31 29#usize) 3#usize

@[reducible]
def FinishModel.Closure1 (H : Type) :=
  Array (Array aspis_core.field.QM31 29#usize) 3#usize

@[reducible]
def FinishModel.Closure (H : Type) := Unit

structure FinishModel.Boundaries where
  fromFn : {T F : Type} → (N : Usize) → core.ops.function.FnMut F Usize T → F → Result (Array T N)
  mask : Array aspis_core.field.QM31 16#usize → Array aspis_core.field.QM31 10#usize →
    aspis_core.field.QM31 → Array aspis_core.field.QM31 10#usize → Result aspis_core.field.QM31
  add : aspis_core.field.QM31 → aspis_core.field.QM31 → Result aspis_core.field.QM31
  mul : aspis_core.field.QM31 → aspis_core.field.QM31 → Result aspis_core.field.QM31
  terminal : pool_v1.pair_forest_semantic_terminal.r0.Public →
    Array (Array aspis_core.field.QM31 29#usize) 3#usize → Array aspis_core.field.QM31 10#usize →
    r1_wire.Challenges → Result (core.result.Result aspis_core.field.QM31 aspis_core.state_only_prefix.r0.Error)
  circle : Array U8 32#usize → FinishModel.CircleRow → Result aspis_core.circle.SecureCirclePoint
  unwrapRoot : core.result.Result (Array U8 32#usize) core.array.TryFromSliceError → Result (Array U8 32#usize)
  claims : r1_wire.Prefix → Result (core.result.Result (Array (Array aspis_core.field.QM31 29#usize) 3#usize) r1_wire.Error)
def FinishModel.payload
  (self : r1_wire.Prefix) (row : Std.U8) :
  Result (core.result.Result (Slice Std.U8) r1_wire.Error)
  := do
  let r ← r1_wire.Prefix.record self row
  let cf ← core.result.Result.Insts.CoreOpsTry.branch r
  match cf with
  | core.ops.control_flow.ControlFlow.Continue val =>
    let s ←
      core.slice.index.Slice.index
        (core.slice.index.SliceIndexRangeFromUsizeSlice Std.U8) val
        { start := 5#usize }
    ok (core.result.Result.Ok s)
  | core.ops.control_flow.ControlFlow.Break residual =>
    core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
      (Slice Std.U8) (core.convert.FromSame r1_wire.Error) residual

def
  FinishModel.pointEq
  (self : aspis_core.circle.SecureCirclePoint)
  (other : aspis_core.circle.SecureCirclePoint) :
  Result Bool
  := do
  let b ← aspis_core.field.QM31.Insts.CoreCmpPartialEqQM31.eq self.x other.x
  if b
  then aspis_core.field.QM31.Insts.CoreCmpPartialEqQM31.eq self.y other.y
  else ok false

def FinishModel.circle_validated (B : FinishModel.Boundaries)
  {H : Type} (aspis_coreDigest32Inst : aspis_core.Digest32 H)
  (self : r1_wire.SemanticTranscript H) (record1 : r1_wire.ValidatedRecord) :
  Result ((core.result.Result aspis_core.circle.SecureCirclePoint
    r1_wire.Error) × (r1_wire.SemanticTranscript H))
  := do
  let row ← r1_wire.ValidatedRecord.impl.row record1
  match row with
  | 25#uscalar =>
    let s ← r1_wire.ValidatedRecord.impl.framed record1
    let (r, self1) ←
      r1_wire.SemanticTranscript.sample_block_validated aspis_coreDigest32Inst
        self 25#u8 s
    let cf ← core.result.Result.Insts.CoreOpsTry.branch r
    match cf with
    | core.ops.control_flow.ControlFlow.Continue val =>
      let scp ← B.circle val FinishModel.CircleRow.First
      ok (core.result.Result.Ok scp, self1)
    | core.ops.control_flow.ControlFlow.Break residual =>
      let r1 ←
        core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
          aspis_core.circle.SecureCirclePoint (core.convert.FromSame
          r1_wire.Error) residual
      ok (r1, self1)
  | 26#uscalar =>
    let s ← r1_wire.ValidatedRecord.impl.framed record1
    let (r, self1) ←
      r1_wire.SemanticTranscript.sample_block_validated aspis_coreDigest32Inst
        self 26#u8 s
    let cf ← core.result.Result.Insts.CoreOpsTry.branch r
    match cf with
    | core.ops.control_flow.ControlFlow.Continue val =>
      let scp ← B.circle val FinishModel.CircleRow.Second
      ok (core.result.Result.Ok scp, self1)
    | core.ops.control_flow.ControlFlow.Break residual =>
      let r1 ←
        core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
          aspis_core.circle.SecureCirclePoint (core.convert.FromSame
          r1_wire.Error) residual
      ok (r1, self1)
  | _ => ok (core.result.Result.Err r1_wire.Error.InvalidRow, self)

def
  FinishModel.closureFn2
  {H : Type} (aspis_coreDigest32Inst : aspis_core.Digest32 H)
  (c : FinishModel.Closure2 H) (tupled_args : Std.Usize) :
  Result (aspis_core.field.QM31 × (FinishModel.Closure2 H))
  := do
  let i ← 16#usize + tupled_args
  let a ← Array.index_usize c 0#usize
  let q ← Array.index_usize a i
  ok (q, c)

def
  FinishModel.closureFn3
  {H : Type} (aspis_coreDigest32Inst : aspis_core.Digest32 H)
  (c : FinishModel.Closure2 H) (i : Std.Usize) :
  Result aspis_core.field.QM31
  := do
  let (q, _) ←
    FinishModel.closureFn2
      aspis_coreDigest32Inst c i
  ok q

@[reducible]
def
  FinishModel.closureFn4
  {H : Type} (aspis_coreDigest32Inst : aspis_core.Digest32 H) :
  core.ops.function.FnOnce (FinishModel.Closure2 H) Std.Usize
  aspis_core.field.QM31 := {
  call_once :=
    FinishModel.closureFn3
    aspis_coreDigest32Inst
}

@[reducible]
def
  FinishModel.closureFn5
  {H : Type} (aspis_coreDigest32Inst : aspis_core.Digest32 H) :
  core.ops.function.FnMut (FinishModel.Closure2 H) Std.Usize
  aspis_core.field.QM31 := {
  FnOnceInst :=
    FinishModel.closureFn4
    aspis_coreDigest32Inst
  call_mut :=
    FinishModel.closureFn2
    aspis_coreDigest32Inst
}

def
  FinishModel.closureFn6
  {H : Type} (aspis_coreDigest32Inst : aspis_core.Digest32 H)
  (c : FinishModel.Closure1 H) (tupled_args : Std.Usize) :
  Result (aspis_core.field.QM31 × (FinishModel.Closure1 H))
  := do
  let a ← Array.index_usize c 0#usize
  let q ← Array.index_usize a tupled_args
  ok (q, c)

def
  FinishModel.closureFn7
  {H : Type} (aspis_coreDigest32Inst : aspis_core.Digest32 H)
  (c : FinishModel.Closure1 H) (i : Std.Usize) :
  Result aspis_core.field.QM31
  := do
  let (q, _) ←
    FinishModel.closureFn6
      aspis_coreDigest32Inst c i
  ok q

@[reducible]
def
  FinishModel.closureFn8
  {H : Type} (aspis_coreDigest32Inst : aspis_core.Digest32 H) :
  core.ops.function.FnOnce (FinishModel.Closure1 H) Std.Usize
  aspis_core.field.QM31 := {
  call_once :=
    FinishModel.closureFn7
    aspis_coreDigest32Inst
}

@[reducible]
def
  FinishModel.closureFn9
  {H : Type} (aspis_coreDigest32Inst : aspis_core.Digest32 H) :
  core.ops.function.FnMut (FinishModel.Closure1 H) Std.Usize
  aspis_core.field.QM31 := {
  FnOnceInst :=
    FinishModel.closureFn8
    aspis_coreDigest32Inst
  call_mut :=
    FinishModel.closureFn6
    aspis_coreDigest32Inst
}

def
  FinishModel.closureFn10
  {H : Type} (aspis_coreDigest32Inst : aspis_core.Digest32 H)
  (c : FinishModel.Closure H)
  (tupled_args : aspis_core.state_only_prefix.r0.Error) :
  Result r1_wire.Error
  := do
  ok r1_wire.Error.Public

@[reducible]
def
  FinishModel.closureFn11
  {H : Type} (aspis_coreDigest32Inst : aspis_core.Digest32 H) :
  core.ops.function.FnOnce (FinishModel.Closure H)
  aspis_core.state_only_prefix.r0.Error r1_wire.Error := {
  call_once :=
    FinishModel.closureFn10
    aspis_coreDigest32Inst
}

def FinishModel.finish (R : RoundModel.Boundaries) (B : FinishModel.Boundaries)
  {H : Type} (aspis_coreDigest32Inst : aspis_core.Digest32 H)
  (public1 : pool_v1.pair_forest_semantic_terminal.r0.Public)
  (prefix1 : r1_wire.Prefix) (transcript : r1_wire.SemanticTranscript H)
  (challenges : r1_wire.Challenges)
  (obs : Option (verifier.Phase → Result Unit)) :
  Result (core.result.Result (r1_semantic.Verified H) r1_wire.Error)
  := do
  let r ←
    RoundModel.rounds R aspis_coreDigest32Inst prefix1 transcript
  let cf ← core.result.Result.Insts.CoreOpsTry.branch r
  match cf with
  | core.ops.control_flow.ControlFlow.Continue val =>
    let (running, alpha, transcript1) := val
    VerifyPrefix.mark obs 2#u8
    let r1 ← B.claims prefix1
    let cf1 ← core.result.Result.Insts.CoreOpsTry.branch r1
    match cf1 with
    | core.ops.control_flow.ControlFlow.Continue val1 =>
      let r2 ←
        B.terminal public1
          val1 alpha challenges
      let r3 ←
        core.result.Result.map_err
          (FinishModel.closureFn11
          aspis_coreDigest32Inst) r2 ()
      let cf2 ← core.result.Result.Insts.CoreOpsTry.branch r3
      match cf2 with
      | core.ops.control_flow.ControlFlow.Continue val2 =>
        VerifyPrefix.mark obs 3#u8
        let a ←
          B.fromFn 16#usize
            (FinishModel.closureFn9
            aspis_coreDigest32Inst) val1
        let a1 ←
          B.fromFn 10#usize
            (FinishModel.closureFn5
            aspis_coreDigest32Inst) val1
        let a2 ← Array.index_usize val1 0#usize
        let q ← Array.index_usize a2 27#usize
        let mask ←
          B.mask a a1 q
            alpha
        let r4 ← r1_wire.Prefix.validated_record prefix1 25#u8
        let cf3 ← core.result.Result.Insts.CoreOpsTry.branch r4
        match cf3 with
        | core.ops.control_flow.ControlFlow.Continue vr =>
          let r5 ← R.decode 29#usize vr 87#usize
          let cf4 ← core.result.Result.Insts.CoreOpsTry.branch r5
          match cf4 with
          | core.ops.control_flow.ControlFlow.Continue val3 =>
            let q1 ← B.mul challenges.eta val2
            let q2 ← B.add mask q1
            let q3 ← Array.index_usize val3 28#usize
            let masked_terminal ← B.add q2 q3
            let b ←
              core.cmp.PartialEq.ne.trait_default
                aspis_core.field.QM31.Insts.CoreCmpPartialEqQM31 running
                masked_terminal
            if b
            then ok (core.result.Result.Err r1_wire.Error.Terminal)
            else
              VerifyPrefix.mark obs 4#u8
              let state_before_z0 ←
                r1_wire.SemanticTranscript.impl.state aspis_coreDigest32Inst
                  transcript1
              let cf5 ← core.result.Result.Insts.CoreOpsTry.branch r4
              match cf5 with
              | core.ops.control_flow.ControlFlow.Continue vr1 =>
                let (r6, transcript2) ←
                  FinishModel.circle_validated B
                    aspis_coreDigest32Inst transcript1 vr1
                let cf6 ← core.result.Result.Insts.CoreOpsTry.branch r6
                match cf6 with
                | core.ops.control_flow.ControlFlow.Continue val4 =>
                  let r7 ← r1_wire.Prefix.validated_record prefix1 26#u8
                  let cf7 ← core.result.Result.Insts.CoreOpsTry.branch r7
                  match cf7 with
                  | core.ops.control_flow.ControlFlow.Continue vr2 =>
                    let r8 ←
                      R.decode 29#usize vr2 0#usize
                    let cf8 ← core.result.Result.Insts.CoreOpsTry.branch r8
                    match cf8 with
                    | core.ops.control_flow.ControlFlow.Continue val5 =>
                      let cf9 ← core.result.Result.Insts.CoreOpsTry.branch r7
                      match cf9 with
                      | core.ops.control_flow.ControlFlow.Continue vr3 =>
                        let (r9, transcript3) ←
                          FinishModel.circle_validated B
                            aspis_coreDigest32Inst transcript2 vr3
                        let cf10 ←
                          core.result.Result.Insts.CoreOpsTry.branch r9
                        match cf10 with
                        | core.ops.control_flow.ControlFlow.Continue val6 =>
                          VerifyPrefix.mark obs 5#u8
                          let b1 ←
                            FinishModel.pointEq
                              val4 val6
                          if b1
                          then
                            ok (core.result.Result.Err
                              r1_wire.Error.EqualCirclePoints)
                          else
                            let r10 ← FinishModel.payload prefix1 2#u8
                            let cf11 ←
                              core.result.Result.Insts.CoreOpsTry.branch r10
                            match cf11 with
                            | core.ops.control_flow.ControlFlow.Continue val7
                              =>
                              let r11 ←
                                core.array.TryFromArrayCopySlice.try_from
                                  32#usize core.marker.CopyU8 val7
                              let a3 ←
                                B.unwrapRoot r11
                              ok (core.result.Result.Ok
                                {
                                  roots :=
                                    (Array.make 2#usize [
                                      prefix1.c1_root, a3
                                      ]),
                                  challenges,
                                  alpha,
                                  claims := val1,
                                  extra := val3,
                                  before_z1 := val5,
                                  state_before_z0,
                                  z := (Array.make 2#usize [ val4, val6 ]),
                                  transcript := transcript3
                                })
                            | core.ops.control_flow.ControlFlow.Break residual
                              =>
                              core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
                                (r1_semantic.Verified H) (core.convert.FromSame
                                r1_wire.Error) residual
                        | core.ops.control_flow.ControlFlow.Break residual =>
                          core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
                            (r1_semantic.Verified H) (core.convert.FromSame
                            r1_wire.Error) residual
                      | core.ops.control_flow.ControlFlow.Break residual =>
                        core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
                          (r1_semantic.Verified H) (core.convert.FromSame
                          r1_wire.Error) residual
                    | core.ops.control_flow.ControlFlow.Break residual =>
                      core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
                        (r1_semantic.Verified H) (core.convert.FromSame
                        r1_wire.Error) residual
                  | core.ops.control_flow.ControlFlow.Break residual =>
                    core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
                      (r1_semantic.Verified H) (core.convert.FromSame
                      r1_wire.Error) residual
                | core.ops.control_flow.ControlFlow.Break residual =>
                  core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
                    (r1_semantic.Verified H) (core.convert.FromSame
                    r1_wire.Error) residual
              | core.ops.control_flow.ControlFlow.Break residual =>
                core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
                  (r1_semantic.Verified H) (core.convert.FromSame
                  r1_wire.Error) residual
          | core.ops.control_flow.ControlFlow.Break residual =>
            core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
              (r1_semantic.Verified H) (core.convert.FromSame r1_wire.Error)
              residual
        | core.ops.control_flow.ControlFlow.Break residual =>
          core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
            (r1_semantic.Verified H) (core.convert.FromSame r1_wire.Error)
            residual
      | core.ops.control_flow.ControlFlow.Break residual =>
        core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
          (r1_semantic.Verified H) (core.convert.FromSame r1_wire.Error)
          residual
    | core.ops.control_flow.ControlFlow.Break residual =>
      core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
        (r1_semantic.Verified H) (core.convert.FromSame r1_wire.Error) residual
  | core.ops.control_flow.ControlFlow.Break residual =>
    core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
      (r1_semantic.Verified H) (core.convert.FromSame r1_wire.Error) residual

#print axioms FinishModel.payload
#print axioms FinishModel.pointEq
#print axioms FinishModel.circle_validated
#print axioms FinishModel.closureFn2
#print axioms FinishModel.closureFn3
#print axioms FinishModel.closureFn4
#print axioms FinishModel.closureFn5
#print axioms FinishModel.closureFn6
#print axioms FinishModel.closureFn7
#print axioms FinishModel.closureFn8
#print axioms FinishModel.closureFn9
#print axioms FinishModel.closureFn10
#print axioms FinishModel.closureFn11
#print axioms FinishModel.finish
end AspisR1PublicPreparation
