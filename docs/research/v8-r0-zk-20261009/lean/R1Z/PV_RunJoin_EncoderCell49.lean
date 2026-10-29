import R1Z.PV_DL_EncoderFill
import R1Z.PV_RunJoin_WeightUpdate46
import R1Z.ProverCommitBasisCounter47
set_option autoImplicit false
namespace R1Z.PV_RunJoin_EncoderCell49
open Aeneas Aeneas.Std Result ProverRwFull
open PV_B2_F_ConstructorCarrier (amap)
open PV_RunJoin_WeightMap46 (mapResult)
abbrev S := AspisR1ProducerRelease47.field.wide_exact.WideExact

theorem complete {E : Type} (inst : aspis_core.r0.scalar.CodeField E) (f : S → E)
    (hm : ∀ a b, inst.mul (f a) (f b)=mapResult f (AspisR1ProducerRelease47.field.wide_exact.WideExact.mul a b))
    (out : Array S 512#usize) (width j : Usize) (factor : S) :
    PV_CB_OwnedEncoder.owned.basis_cell inst (amap f out) width j (f factor)=
      mapResult (amap f) (do
        let v ← Array.index_usize out j
        let product ← AspisR1ProducerRelease47.field.wide_exact.WideExact.mul v factor
        Array.update out (Usize.wrapping_add width j) product) := by
  unfold PV_CB_OwnedEncoder.owned.basis_cell
  rw [PV_RunJoin_WeightMap46.index]
  cases h : Array.index_usize out j with
  | fail e => rfl
  | div => rfl
  | ok v =>
    simp only [mapResult,PV_B2_E_OrdinaryOriginal.mapResult,bind_tc_ok,hm,lift]
    cases hmul : AspisR1ProducerRelease47.field.wide_exact.WideExact.mul v factor with
    | fail e => rfl
    | div => rfl
    | ok x =>
      simp only [PV_B2_E_OrdinaryOriginal.mapResult,bind_tc_ok]
      exact PV_RunJoin_WeightUpdate46.complete f out _ x
#print axioms complete
end R1Z.PV_RunJoin_EncoderCell49
