import AspisR1ProducerRelease47.Basis
import AspisR1ProducerRelease47.Opening48
import AspisR1ProducerRelease47.Pairs
/-! Extracted inverse fibre transform, with identical arithmetic callees rebound to the
previously proved release extraction. bind-encoder-phi.py checks every reused
callee declaration body byte-for-byte. No external template is installed. -/
open Aeneas Aeneas.Std Result ControlFlow Error
noncomputable section
namespace AspisR1ProducerRelease47
def encoder53.phi_inverse
  (x : field.wide_exact.WideExact) (y : field.wide_exact.WideExact)
  (h : Array field.wide_exact.WideExact 4#usize) :
  Result (Array field.wide_exact.WideExact 4#usize)
  := do
  let h0 ← Array.index_usize h 0#usize
  let h1 ← Array.index_usize h 1#usize
  let h2 ← Array.index_usize h 2#usize
  let h3 ← Array.index_usize h 3#usize
  let a ← field.wide_exact.WideExact.mul y h1
  let b ← field.wide_exact.WideExact.mul x h2
  let we ← field.wide_exact.WideExact.mul x y
  let c ← field.wide_exact.WideExact.mul we h3
  let we1 ← field.wide_exact.WideExact.add h0 a
  let we2 ← field.wide_exact.WideExact.add we1 b
  let we3 ← field.wide_exact.WideExact.add we2 c
  let we4 ← field.wide_exact.WideExact.sub h0 a
  let we5 ← field.wide_exact.WideExact.add we4 b
  let we6 ← field.wide_exact.WideExact.sub we5 c
  let we7 ← field.wide_exact.WideExact.sub we4 b
  let we8 ← field.wide_exact.WideExact.add we7 c
  let we9 ← field.wide_exact.WideExact.sub we1 b
  let we10 ← field.wide_exact.WideExact.sub we9 c
  ok (Array.make 4#usize [ we3, we6, we8, we10 ])

end AspisR1ProducerRelease47
