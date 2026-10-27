import SAQ_LineSource
set_option autoImplicit false
noncomputable section
namespace AspisR1.FIp_CircleSource
open Aeneas Aeneas.Std Result
open AspisR1CurrentWide AspisR1CurrentWide.Proof
/-- Retained extracted circle fold, with the same concrete arithmetic dictionary as the installed line fold. -/
def circle (alpha : E) (a : Array E 4#usize) (inverse : Array U32 5#usize) : Result E
:= do
  let ix ← Array.index_usize inverse 0#usize
  let iy ← Array.index_usize inverse 1#usize
  let a1 ← Array.index_usize a 0#usize
  let b ← Array.index_usize a 1#usize
  let c ← Array.index_usize a 2#usize
  let d ← Array.index_usize a 3#usize
  let we ← field.wide_exact.WideExact.add a1 b
  let we1 ← field.wide_exact.WideExact.add we c
  let we2 ← field.wide_exact.WideExact.add we1 d
  let h0 ← field.wide_exact.WideExact.mul_m31 we2 SAQ_LineSource.quarter
  let we3 ← field.wide_exact.WideExact.sub a1 b
  let we4 ← field.wide_exact.WideExact.sub we3 c
  let we5 ← field.wide_exact.WideExact.add we4 d
  let m ← field.M31.mul SAQ_LineSource.quarter iy
  let h1 ← field.wide_exact.WideExact.mul_m31 we5 m
  let we6 ← field.wide_exact.WideExact.sub we c
  let we7 ← field.wide_exact.WideExact.sub we6 d
  let m1 ← field.M31.mul SAQ_LineSource.quarter ix
  let h2 ← field.wide_exact.WideExact.mul_m31 we7 m1
  let we8 ← field.wide_exact.WideExact.add we3 c
  let we9 ← field.wide_exact.WideExact.sub we8 d
  let m2 ← field.M31.mul m1 iy
  let h3 ← field.wide_exact.WideExact.mul_m31 we9 m2
  let we10 ← field.wide_exact.WideExact.mul alpha h3
  let we11 ← field.wide_exact.WideExact.add h2 we10
  let we12 ← field.wide_exact.WideExact.mul alpha we11
  let we13 ← field.wide_exact.WideExact.add h1 we12
  let we14 ← field.wide_exact.WideExact.mul alpha we13
  field.wide_exact.WideExact.add h0 we14

#print circle
end AspisR1.FIp_CircleSource
end
