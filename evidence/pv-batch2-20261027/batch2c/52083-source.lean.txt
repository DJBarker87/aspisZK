import R1Z.PV_B2_C_RawWeights251Funs
set_option autoImplicit false
namespace PV_B2_C_EmissionProbe
open Aeneas Aeneas.Std Result PV_B2_251c1
abbrev K := aspis_core.field.QM31
abbrev E := aspis_core.field.wide_exact.WideExact

def limbs (x : E) : List Nat :=
  [x.c0.c0.a.val,x.c0.c0.b.val,x.c0.c1.a.val,x.c0.c1.b.val,
   x.c1.c0.a.val,x.c1.c0.b.val,x.c1.c1.a.val,x.c1.c1.b.val]

def weights (v : transport.Variant) : host_weights.Weights :=
  {variant := v,
   factors := Array.repeat 5#usize (Array.repeat 5#usize
      (Array.repeat 4#usize aspis_core.field.QM31.ONE)),
   points := Array.repeat 3#usize (Array.repeat 10#usize aspis_core.field.QM31.ONE),
   extra := Array.repeat 2#usize aspis_core.field.QM31.ONE}

/-- Finite executable differential input, not a universal source theorem. -/
def probe (v : transport.Variant) : Result (List (List Nat)) := do
  let out ← host_weights.materialize_values (weights v)
    aspis_core.field.wide_exact.WideExact.ONE
    (Array.repeat 1024#usize aspis_core.field.wide_exact.WideExact.ZERO)
  let x0 ← Array.index_usize out 0#usize
  let x1 ← Array.index_usize out 1#usize
  let x13 ← Array.index_usize out 13#usize
  let x56 ← Array.index_usize out 56#usize
  let x317 ← Array.index_usize out 317#usize
  let x1023 ← Array.index_usize out 1023#usize
  ok ([x0,x1,x13,x56,x317,x1023].map limbs)

#eval probe .S1
#eval probe .S2
#eval probe .D
#print axioms limbs
#print axioms weights
#print axioms probe
end PV_B2_C_EmissionProbe
