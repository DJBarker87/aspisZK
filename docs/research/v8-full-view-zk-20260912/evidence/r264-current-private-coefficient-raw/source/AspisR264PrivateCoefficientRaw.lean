import AspisR259PrivateInputRaw
open Aeneas Aeneas.Std Result ControlFlow Error
open AspisR259PrivateInputRaw
open AspisR249R110Raw
open AspisR156FullFreeze
set_option linter.dupNamespace false
set_option linter.hashCommand false
set_option linter.unusedVariables false

namespace AspisR264PrivateCoefficientRaw

/-- [aspis_v8_performance_host::circle_norm::joined_inverse::line_norm::r110_norm::{aspis_v8_performance_host::circle_norm::joined_inverse::line_norm::r110_norm::Coeff110}::new::closure]
    Source: '../r110_norm.rs', lines 48:17-48:68 -/
@[reducible]
def circle_norm.joined_inverse.line_norm.r110_norm.Coeff110.new.closure := Unit

/-- [aspis_v8_performance_host::circle_norm::joined_inverse::line_norm::r110_norm::{aspis_v8_performance_host::circle_norm::joined_inverse::line_norm::r110_norm::Coeff110}::new::closure#1]
    Source: '../r110_norm.rs', lines 49:18-49:88 -/
@[reducible]
def circle_norm.joined_inverse.line_norm.r110_norm.Coeff110.new.closure_1 :=
Unit

/-- [aspis_v8_performance_host::circle_norm::joined_inverse::line_norm::r110_norm::Coeff110]
    Source: '../r110_norm.rs', lines 44:0-44:23 -/
@[reducible]
def circle_norm.joined_inverse.line_norm.r110_norm.Coeff110 :=
  Array circle_norm.joined_inverse.line_norm.r110_norm.C 5#usize

/-- [aspis_v8_performance_host::circle_norm::joined_inverse::line_norm::r110_norm::{aspis_v8_performance_host::circle_norm::joined_inverse::line_norm::r110_norm::Coeff110}::new::{impl core::ops::function::Fn<([aspis_v8_performance_host::circle_norm::joined_inverse::line_norm::r110_norm::C; 2usize],), aspis_v8_performance_host::circle_norm::joined_inverse::line_norm::r110_norm::C> for aspis_v8_performance_host::circle_norm::joined_inverse::line_norm::r110_norm::{aspis_v8_performance_host::circle_norm::joined_inverse::line_norm::r110_norm::Coeff110}::new::closure}::call]:
    Source: '../r110_norm.rs', lines 48:17-48:68 -/
def
  circle_norm.joined_inverse.line_norm.r110_norm.Coeff110.new.closure.Insts.CoreOpsFunctionFnTupleArrayC2C.call
  (c : circle_norm.joined_inverse.line_norm.r110_norm.Coeff110.new.closure)
  (tupled_args : Array circle_norm.joined_inverse.line_norm.r110_norm.C
  2#usize) :
  Result circle_norm.joined_inverse.line_norm.r110_norm.C
  := do
  let c1 ← Array.index_usize tupled_args 0#usize
  let c2 ← circle_norm.joined_inverse.line_norm.r110_norm.C.square c1
  let c3 ← Array.index_usize tupled_args 1#usize
  let c4 ← circle_norm.joined_inverse.line_norm.r110_norm.C.square c3
  let c5 ← circle_norm.joined_inverse.line_norm.r110_norm.C.times_r c4
  circle_norm.joined_inverse.line_norm.r110_norm.C.sub c2 c5

/-- [aspis_v8_performance_host::circle_norm::joined_inverse::line_norm::r110_norm::{aspis_v8_performance_host::circle_norm::joined_inverse::line_norm::r110_norm::Coeff110}::new::{impl core::ops::function::Fn<([aspis_v8_performance_host::circle_norm::joined_inverse::line_norm::r110_norm::C; 2usize], [aspis_v8_performance_host::circle_norm::joined_inverse::line_norm::r110_norm::C; 2usize]), aspis_v8_performance_host::circle_norm::joined_inverse::line_norm::r110_norm::C> for aspis_v8_performance_host::circle_norm::joined_inverse::line_norm::r110_norm::{aspis_v8_performance_host::circle_norm::joined_inverse::line_norm::r110_norm::Coeff110}::new::closure#1}::call]:
    Source: '../r110_norm.rs', lines 49:18-49:88 -/
def
  circle_norm.joined_inverse.line_norm.r110_norm.Coeff110.new.closure_1.Insts.CoreOpsFunctionFnPairArrayC2ArrayC2C.call
  (c : circle_norm.joined_inverse.line_norm.r110_norm.Coeff110.new.closure_1)
  (tupled_args : ((Array circle_norm.joined_inverse.line_norm.r110_norm.C
  2#usize) × (Array circle_norm.joined_inverse.line_norm.r110_norm.C
  2#usize))) :
  Result circle_norm.joined_inverse.line_norm.r110_norm.C
  := do
  let (x, y) := tupled_args
  let c1 ← Array.index_usize x 0#usize
  let c2 ← Array.index_usize y 0#usize
  let c3 ← circle_norm.joined_inverse.line_norm.r110_norm.C.mul c1 c2
  let c4 ← Array.index_usize x 1#usize
  let c5 ← Array.index_usize y 1#usize
  let c6 ← circle_norm.joined_inverse.line_norm.r110_norm.C.mul c4 c5
  let c7 ← circle_norm.joined_inverse.line_norm.r110_norm.C.times_r c6
  let c8 ← circle_norm.joined_inverse.line_norm.r110_norm.C.sub c3 c7
  circle_norm.joined_inverse.line_norm.r110_norm.C.double c8

/-- [aspis_v8_performance_host::circle_norm::joined_inverse::line_norm::r110_norm::{aspis_v8_performance_host::circle_norm::joined_inverse::line_norm::r110_norm::Coeff110}::new]:
    Source: '../r110_norm.rs', lines 46:4-52:5 -/
def circle_norm.joined_inverse.line_norm.r110_norm.Coeff110.new
  (a : Array aspis_core.field.QM31 3#usize) :
  Result (Option circle_norm.joined_inverse.line_norm.r110_norm.Coeff110)
  := do
  let a1 ← Array.index_usize a 0#usize
  let b ← Array.index_usize a 1#usize
  let c ← Array.index_usize a 2#usize
  let o ← circle_norm.joined_inverse.line_norm.r110_norm.C.input a1.c0
  let cf ← core.option.Option.Insts.CoreOpsTry_traitTry.branch o
  match cf with
  | core.ops.control_flow.ControlFlow.Continue val =>
    let o1 ← circle_norm.joined_inverse.line_norm.r110_norm.C.input a1.c1
    let cf1 ← core.option.Option.Insts.CoreOpsTry_traitTry.branch o1
    match cf1 with
    | core.ops.control_flow.ControlFlow.Continue val1 =>
      let o2 ← circle_norm.joined_inverse.line_norm.r110_norm.C.input b.c0
      let cf2 ← core.option.Option.Insts.CoreOpsTry_traitTry.branch o2
      match cf2 with
      | core.ops.control_flow.ControlFlow.Continue val2 =>
        let o3 ← circle_norm.joined_inverse.line_norm.r110_norm.C.input b.c1
        let cf3 ← core.option.Option.Insts.CoreOpsTry_traitTry.branch o3
        match cf3 with
        | core.ops.control_flow.ControlFlow.Continue val3 =>
          let o4 ←
            circle_norm.joined_inverse.line_norm.r110_norm.C.input c.c0
          let cf4 ← core.option.Option.Insts.CoreOpsTry_traitTry.branch o4
          match cf4 with
          | core.ops.control_flow.ControlFlow.Continue val4 =>
            let o5 ←
              circle_norm.joined_inverse.line_norm.r110_norm.C.input c.c1
            let cf5 ← core.option.Option.Insts.CoreOpsTry_traitTry.branch o5
            match cf5 with
            | core.ops.control_flow.ControlFlow.Continue val5 =>
              let nc ←
                circle_norm.joined_inverse.line_norm.r110_norm.Coeff110.new.closure.Insts.CoreOpsFunctionFnTupleArrayC2C.call
                  () (Array.make 2#usize [ val4, val5 ])
              let c1 ←
                circle_norm.joined_inverse.line_norm.r110_norm.Coeff110.new.closure.Insts.CoreOpsFunctionFnTupleArrayC2C.call
                  () (Array.make 2#usize [ val2, val3 ])
              let c2 ←
                circle_norm.joined_inverse.line_norm.r110_norm.C.sub c1 nc
              let half ←
                circle_norm.joined_inverse.line_norm.r110_norm.C.half c2
              let c3 ←
                circle_norm.joined_inverse.line_norm.r110_norm.Coeff110.new.closure.Insts.CoreOpsFunctionFnTupleArrayC2C.call
                  () (Array.make 2#usize [ val, val1 ])
              let c4 ←
                circle_norm.joined_inverse.line_norm.r110_norm.C.add c3 nc
              let c5 ←
                circle_norm.joined_inverse.line_norm.r110_norm.C.add c4 half
              let c6 ←
                circle_norm.joined_inverse.line_norm.r110_norm.Coeff110.new.closure_1.Insts.CoreOpsFunctionFnPairArrayC2ArrayC2C.call
                  () (Array.make 2#usize [ val, val1 ],
                  Array.make 2#usize [ val2, val3 ])
              let c7 ←
                circle_norm.joined_inverse.line_norm.r110_norm.Coeff110.new.closure_1.Insts.CoreOpsFunctionFnPairArrayC2ArrayC2C.call
                  () (Array.make 2#usize [ val, val1 ],
                  Array.make 2#usize [ val4, val5 ])
              let c8 ←
                circle_norm.joined_inverse.line_norm.r110_norm.Coeff110.new.closure_1.Insts.CoreOpsFunctionFnPairArrayC2ArrayC2C.call
                  () (Array.make 2#usize [ val2, val3 ],
                  Array.make 2#usize [ val4, val5 ])
              ok (some (Array.make 5#usize [ c5, half, c6, c7, c8 ]))
            | core.ops.control_flow.ControlFlow.Break residual =>
              core.option.Option.Insts.CoreOpsTry_traitFromResidualOptionInfallible.from_residual
                circle_norm.joined_inverse.line_norm.r110_norm.Coeff110
                residual
          | core.ops.control_flow.ControlFlow.Break residual =>
            core.option.Option.Insts.CoreOpsTry_traitFromResidualOptionInfallible.from_residual
              circle_norm.joined_inverse.line_norm.r110_norm.Coeff110 residual
        | core.ops.control_flow.ControlFlow.Break residual =>
          core.option.Option.Insts.CoreOpsTry_traitFromResidualOptionInfallible.from_residual
            circle_norm.joined_inverse.line_norm.r110_norm.Coeff110 residual
      | core.ops.control_flow.ControlFlow.Break residual =>
        core.option.Option.Insts.CoreOpsTry_traitFromResidualOptionInfallible.from_residual
          circle_norm.joined_inverse.line_norm.r110_norm.Coeff110 residual
    | core.ops.control_flow.ControlFlow.Break residual =>
      core.option.Option.Insts.CoreOpsTry_traitFromResidualOptionInfallible.from_residual
        circle_norm.joined_inverse.line_norm.r110_norm.Coeff110 residual
  | core.ops.control_flow.ControlFlow.Break residual =>
    core.option.Option.Insts.CoreOpsTry_traitFromResidualOptionInfallible.from_residual
      circle_norm.joined_inverse.line_norm.r110_norm.Coeff110 residual

/-- [aspis_v8_performance_host::circle_norm::joined_inverse::line_norm::r110_norm::{aspis_v8_performance_host::circle_norm::joined_inverse::line_norm::r110_norm::Coeff110}::four]:
    Source: '../r110_norm.rs', lines 53:21-59:5 -/
def circle_norm.joined_inverse.line_norm.r110_norm.Coeff110.four
  (self : circle_norm.joined_inverse.line_norm.r110_norm.Coeff110)
  (x : circle_norm.joined_inverse.line_norm.r110_norm.B)
  (y : circle_norm.joined_inverse.line_norm.r110_norm.B)
  (t : circle_norm.joined_inverse.line_norm.r110_norm.B) :
  Result (Array circle_norm.joined_inverse.line_norm.r110_norm.C 4#usize)
  := do
  let c ← Array.index_usize self 0#usize
  let c1 ← Array.index_usize self 1#usize
  let c2 ← circle_norm.joined_inverse.line_norm.r110_norm.C.mul_m c1 t
  let even ← circle_norm.joined_inverse.line_norm.r110_norm.C.add c c2
  let c3 ← Array.index_usize self 2#usize
  let odd_x ← circle_norm.joined_inverse.line_norm.r110_norm.C.mul_m c3 x
  let c4 ← Array.index_usize self 3#usize
  let odd_y ← circle_norm.joined_inverse.line_norm.r110_norm.C.mul_m c4 y
  let c5 ← Array.index_usize self 4#usize
  let b ← circle_norm.joined_inverse.line_norm.r110_norm.B.mul x y
  let cross ← circle_norm.joined_inverse.line_norm.r110_norm.C.mul_m c5 b
  let positive ←
    circle_norm.joined_inverse.line_norm.r110_norm.C.add even odd_x
  let negative ←
    circle_norm.joined_inverse.line_norm.r110_norm.C.sub even odd_x
  let plus ← circle_norm.joined_inverse.line_norm.r110_norm.C.add odd_y cross
  let minus ←
    circle_norm.joined_inverse.line_norm.r110_norm.C.sub odd_y cross
  let c6 ← circle_norm.joined_inverse.line_norm.r110_norm.C.add positive plus
  let c7 ← circle_norm.joined_inverse.line_norm.r110_norm.C.sub positive plus
  let c8 ←
    circle_norm.joined_inverse.line_norm.r110_norm.C.sub negative minus
  let c9 ←
    circle_norm.joined_inverse.line_norm.r110_norm.C.add negative minus
  ok (Array.make 4#usize [ c6, c7, c8, c9 ])


#print axioms circle_norm.joined_inverse.line_norm.r110_norm.Coeff110.new.closure
#print axioms circle_norm.joined_inverse.line_norm.r110_norm.Coeff110.new.closure_1
#print axioms circle_norm.joined_inverse.line_norm.r110_norm.Coeff110
#print axioms circle_norm.joined_inverse.line_norm.r110_norm.Coeff110.new.closure.Insts.CoreOpsFunctionFnTupleArrayC2C.call
#print axioms circle_norm.joined_inverse.line_norm.r110_norm.Coeff110.new.closure_1.Insts.CoreOpsFunctionFnPairArrayC2ArrayC2C.call
#print axioms circle_norm.joined_inverse.line_norm.r110_norm.Coeff110.new
#print axioms circle_norm.joined_inverse.line_norm.r110_norm.Coeff110.four
end AspisR264PrivateCoefficientRaw
