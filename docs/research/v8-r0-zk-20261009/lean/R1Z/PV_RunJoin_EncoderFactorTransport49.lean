import R1Z.PV_RunJoin_WeightMap46
import R1Z.PV_DL_EncoderBasis
set_option autoImplicit false
namespace R1Z.PV_RunJoin_EncoderFactorTransport49
open Aeneas Aeneas.Std Result ProverRwFull
open PV_RunJoin_WeightMap46 (mapResult)
def next {S : Type} (mul add sub : S → S → Result S) (one x : S) : Result S := do
  let square ← mul x x
  let doubled ← add square square
  sub doubled one

theorem complete {S E : Type} (inst : aspis_core.r0.scalar.CodeField E) (f : S → E)
    (mul add sub : S → S → Result S) (one : S)
    (hone : inst.ONE=ok (f one))
    (hm : ∀ a b, inst.mul (f a) (f b)=mapResult f (mul a b))
    (ha : ∀ a b, inst.add (f a) (f b)=mapResult f (add a b))
    (hs : ∀ a b, inst.sub (f a) (f b)=mapResult f (sub a b)) (x : S) :
    PV_DL_EncoderBasis.factor inst (f x)=mapResult f (next mul add sub one x) := by
  unfold PV_DL_EncoderBasis.factor next
  rw [hm]
  cases hm0 : mul x x with
  | fail e => rfl
  | div => rfl
  | ok a =>
    simp only [mapResult,PV_B2_E_OrdinaryOriginal.mapResult,bind_tc_ok,ha]
    cases ha0 : add a a with
    | fail e => rfl
    | div => rfl
    | ok b =>
      simp only [PV_B2_E_OrdinaryOriginal.mapResult,bind_tc_ok,hone]
      exact hs b one
#print axioms next
#print axioms complete
end R1Z.PV_RunJoin_EncoderFactorTransport49
