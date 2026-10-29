import R1Z.PV_RunJoin_EncoderCell49
set_option autoImplicit false
namespace R1Z.PV_RunJoin_EncoderFill49
open Aeneas Aeneas.Std Result ProverRwFull
open PV_B2_F_ConstructorCarrier (amap)
open PV_RunJoin_WeightMap46 (mapResult)
open PV_RunJoin_EncoderCell49 (S)
theorem complete {E : Type} (inst : aspis_core.r0.scalar.CodeField E) (f : S → E)
    (hm : ∀ a b, inst.mul (f a) (f b)=mapResult f (AspisR1ProducerRelease47.field.wide_exact.WideExact.mul a b))
    (n : Nat) (out : Array S 512#usize) (width j : Usize) (factor : S) :
    PV_DL_EncoderFill.finite inst width (f factor) n j (amap f out)=
      mapResult (amap f) (ProverCommitBasisCounter47.fillN n out j width factor) := by
  induction n generalizing out j with
  | zero => rfl
  | succ n ih =>
    simp only [PV_DL_EncoderFill.finite,PV_RunJoin_EncoderCell49.complete inst f hm,
      ProverCommitBasisCounter47.fillN]
    symm
    apply PV_RunJoin_WeightMap46.map_bind (amap f) (amap f)
    intro next
    exact (ih next (PV_DL_EncoderRange.advance j)).symm
#print axioms complete
end R1Z.PV_RunJoin_EncoderFill49
