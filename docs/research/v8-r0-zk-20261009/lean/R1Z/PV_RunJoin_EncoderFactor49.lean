import R1Z.PV_RunJoin_EncoderCell49
import R1Z.PV_DL_EncoderBasis
set_option autoImplicit false
namespace R1Z.PV_RunJoin_EncoderFactor49
open Aeneas Aeneas.Std Result ProverRwFull
open PV_RunJoin_WeightMap46 (mapResult)
open PV_RunJoin_EncoderCell49 (S)
def next (x : S) : Result S := do
  let square ← AspisR1ProducerRelease47.field.wide_exact.WideExact.mul x x
  let doubled ← AspisR1ProducerRelease47.field.wide_exact.WideExact.add square square
  AspisR1ProducerRelease47.field.wide_exact.WideExact.sub doubled
    AspisR1ProducerRelease47.field.wide_exact.WideExact.ONE

attribute [local irreducible]
  AspisR1ProducerRelease47.field.wide_exact.WideExact.mul
  AspisR1ProducerRelease47.field.wide_exact.WideExact.add
  AspisR1ProducerRelease47.field.wide_exact.WideExact.sub
  AspisR1ProducerRelease47.field.wide_exact.WideExact.ONE

theorem complete {E : Type} (inst : aspis_core.r0.scalar.CodeField E) (f : S → E)
    (hone : inst.ONE=ok (f AspisR1ProducerRelease47.field.wide_exact.WideExact.ONE))
    (hm : ∀ a b, inst.mul (f a) (f b)=mapResult f (AspisR1ProducerRelease47.field.wide_exact.WideExact.mul a b))
    (ha : ∀ a b, inst.add (f a) (f b)=mapResult f (AspisR1ProducerRelease47.field.wide_exact.WideExact.add a b))
    (hs : ∀ a b, inst.sub (f a) (f b)=mapResult f (AspisR1ProducerRelease47.field.wide_exact.WideExact.sub a b))
    (x : S) : PV_DL_EncoderBasis.factor inst (f x)=mapResult f (next x) := by
  unfold PV_DL_EncoderBasis.factor next
  rw [hm]
  cases hm0 : AspisR1ProducerRelease47.field.wide_exact.WideExact.mul x x with
  | fail e => rfl
  | div => rfl
  | ok a =>
    simp only [mapResult,PV_B2_E_OrdinaryOriginal.mapResult,bind_tc_ok,ha]
    cases ha0 : AspisR1ProducerRelease47.field.wide_exact.WideExact.add a a with
    | fail e => rfl
    | div => rfl
    | ok b =>
      simp only [PV_B2_E_OrdinaryOriginal.mapResult,bind_tc_ok,hone]
      exact hs b _
#print axioms next
#print axioms complete
end R1Z.PV_RunJoin_EncoderFactor49
