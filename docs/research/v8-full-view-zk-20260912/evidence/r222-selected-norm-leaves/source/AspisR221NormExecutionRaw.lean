import AspisR156FullFreeze.FunsCore
open Aeneas Aeneas.Std Result
open AspisR156FullFreeze
set_option autoImplicit false
namespace AspisR221NormExecutionRaw

/-- [aspis_v8_performance_host::circle_norm::times_r]:
    Source: '../circle_norm.rs', lines 7:0-7:80 -/
def circle_norm.times_r
  (z : aspis_core.field.CM31) : Result aspis_core.field.CM31 := do
  let m ← aspis_core.field.M31.double z.a
  let m1 ← aspis_core.field.M31.sub m z.b
  let m2 ← aspis_core.field.M31.double z.b
  let m3 ← aspis_core.field.M31.add z.a m2
  aspis_core.field.CM31.new m1 m3

/-- [aspis_v8_performance_host::circle_norm::norm]:
    Source: '../circle_norm.rs', lines 8:0-8:61 -/
def circle_norm.norm
  (v : aspis_core.field.QM31) : Result aspis_core.field.CM31 := do
  let c ← aspis_core.field.CM31.square v.c0
  let c1 ← aspis_core.field.CM31.square v.c1
  let c2 ← circle_norm.times_r c1
  aspis_core.field.CM31.sub c c2

/-- [aspis_v8_performance_host::circle_norm::polar]:
    Source: '../circle_norm.rs', lines 9:0-9:77 -/
def circle_norm.polar
  (v : aspis_core.field.QM31) (w : aspis_core.field.QM31) :
  Result aspis_core.field.CM31
  := do
  let c ← aspis_core.field.CM31.mul v.c0 w.c0
  let c1 ← aspis_core.field.CM31.mul v.c1 w.c1
  let c2 ← circle_norm.times_r c1
  let c3 ← aspis_core.field.CM31.sub c c2
  aspis_core.field.CM31.double c3


#print axioms circle_norm.times_r
#print axioms circle_norm.norm
#print axioms circle_norm.polar
end AspisR221NormExecutionRaw
