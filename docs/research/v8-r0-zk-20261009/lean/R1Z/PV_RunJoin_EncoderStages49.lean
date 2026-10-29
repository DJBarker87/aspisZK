import R1Z.PV_RunJoin_EncoderFill49
import R1Z.PV_RunJoin_EncoderFactor49
import R1Z.ProverCommitBasisStep47
set_option autoImplicit false
namespace R1Z.PV_RunJoin_EncoderStages49
open Aeneas Aeneas.Std Result ProverRwFull
open PV_B2_F_ConstructorCarrier (amap)
open PV_RunJoin_WeightMap46 (mapResult)
open PV_RunJoin_EncoderCell49 (S)
theorem complete {E : Type} (inst : aspis_core.r0.scalar.CodeField E) (f : S → E)
    (hone : inst.ONE=ok (f AspisR1ProducerRelease47.field.wide_exact.WideExact.ONE))
    (hm : ∀ a b, inst.mul (f a) (f b)=mapResult f (AspisR1ProducerRelease47.field.wide_exact.WideExact.mul a b))
    (ha : ∀ a b, inst.add (f a) (f b)=mapResult f (AspisR1ProducerRelease47.field.wide_exact.WideExact.add a b))
    (hs : ∀ a b, inst.sub (f a) (f b)=mapResult f (AspisR1ProducerRelease47.field.wide_exact.WideExact.sub a b))
    (n : Nat) (out : Array S 512#usize) (width : Usize) (factor : S)
    (rank : width.val*2^n=512) :
    PV_DL_EncoderBasis.finite inst n (amap f out) width (f factor)=
      mapResult (amap f) (ProverCommitBasisCounter47.stagesN n out width factor) := by
  induction n generalizing out width factor with
  | zero => rfl
  | succ n ih =>
    have half := PV_DL_EncoderBasis.half_rank width n rank
    have hv := PV_DL_EncoderBasis.advance_val width half
    have hr : (PV_DL_EncoderBasis.advance width).val*2^n=512 := by
      rw [hv]
      simpa only [Nat.pow_succ,Nat.mul_assoc,Nat.mul_comm,Nat.mul_left_comm] using rank
    rw [PV_DL_EncoderBasis.finite,PV_RunJoin_EncoderFill49.complete inst f hm]
    rw [ProverCommitBasisCounter47.stagesN,ProverCommitBasisCounter47.fill_source width.val _
      (ProverCommitBasisStep47.cast_width width (by omega))]
    cases hfill : ProverCommitBasisCounter47.fillN width.val out 0#usize width factor with
    | fail e => rfl
    | div => rfl
    | ok out1 =>
      simp only [mapResult,PV_B2_E_OrdinaryOriginal.mapResult,bind_tc_ok,
        PV_RunJoin_EncoderFactor49.complete inst f hone hm ha hs]
      change (do let x ← mapResult f (PV_RunJoin_EncoderFactor49.next factor)
                 PV_DL_EncoderBasis.finite inst n (amap f out1) (PV_DL_EncoderBasis.advance width) x)=_
      simpa only [PV_RunJoin_EncoderFactor49.next,Aeneas.Std.bind_assoc_eq,
        mapResult,PV_B2_E_OrdinaryOriginal.mapResult,PV_DL_EncoderBasis.advance] using
        (PV_RunJoin_WeightMap46.map_bind f (amap f) (PV_RunJoin_EncoderFactor49.next factor)
          (fun x => ProverCommitBasisCounter47.stagesN n out1 (PV_DL_EncoderBasis.advance width) x)
          (fun x => PV_DL_EncoderBasis.finite inst n (amap f out1) (PV_DL_EncoderBasis.advance width) x)
          (fun x => (ih out1 _ x hr).symm)).symm
#print axioms complete
end R1Z.PV_RunJoin_EncoderStages49
