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
    simpa only [Aeneas.Std.bind_assoc_eq] using
      PV_RunJoin_WeightMap46.map_bind (amap f) (amap f)
        (do let v ← Array.index_usize out j
            let product ← AspisR1ProducerRelease47.field.wide_exact.WideExact.mul v factor
            Array.update out (Usize.wrapping_add width j) product)
        (fun next => ProverCommitBasisCounter47.fillN n next (Usize.wrapping_add j 1#usize) width factor)
        (fun next => PV_DL_EncoderFill.finite inst width (f factor) n (PV_DL_EncoderRange.advance j) next)
        (fun next => (ih next (PV_DL_EncoderRange.advance j)).symm)
#print axioms complete
end R1Z.PV_RunJoin_EncoderFill49
