import R1Z.PV_AL_CircleOwnedFuns
open Aeneas Aeneas.Std Result
namespace R1Z.PV_AL_CircleDigitEval
set_option autoImplicit false

def limbs (q : PV_AL_CircleOwned.aspis_core.field.QM31) : List Nat :=
  [q.c0.a.val,q.c0.b.val,q.c1.a.val,q.c1.b.val]

#eval (do
  let q ← PV_AL_CircleOwned.shipped_sampler.qm31_sample (Array.repeat 32#usize 0#u8)
  ok (limbs q) : Result (List Nat))
#eval (do
  let q ← PV_AL_CircleOwned.shipped_sampler.qm31_sample (Array.repeat 32#usize 255#u8)
  ok (limbs q) : Result (List Nat))

#print axioms limbs
end R1Z.PV_AL_CircleDigitEval
