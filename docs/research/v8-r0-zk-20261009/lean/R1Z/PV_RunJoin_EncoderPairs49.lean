import R1Z.PV_RunJoin_EncoderPairCell49
import R1Z.PV_RunJoin_EncoderBind49
set_option autoImplicit false
namespace R1Z.PV_RunJoin_EncoderPairs49
open Aeneas Aeneas.Std Result ProverRwFull
open PV_B2_F_ConstructorCarrier (amap)
open PV_RunJoin_WeightMap46 (mapResult)
open PV_RunJoin_EncoderCell49 (S)
open PV_RunJoin_EncoderPairTransport49 (pairMap)
theorem complete {E : Type} (inst : aspis_core.r0.scalar.CodeField E) (f : S → E)
    (hm : ∀ a b, inst.mul (f a) (f b)=mapResult f (AspisR1ProducerRelease47.field.wide_exact.WideExact.mul a b))
    (ha : ∀ a b, inst.add (f a) (f b)=mapResult f (AspisR1ProducerRelease47.field.wide_exact.WideExact.add a b))
    (q : Array S 1024#usize) (basis : Array S 512#usize)
    (n : Nat) (j : Usize) (rank : j.val+n=512) (p0 p1 : S) :
    PV_DL_EncoderFold.finite inst (amap f q) (amap f basis) n j (f p0) (f p1)=
      mapResult (pairMap f) (ProverCommitNativePair48.range q basis n j (p0,p1)) := by
  induction n generalizing j p0 p1 with
  | zero => rfl
  | succ n ih =>
    have hj : j.val<512 := by omega
    have hr : (PV_DL_EncoderRange.advance j).val+n=512 := by
      rw [PV_DL_EncoderRange.advance_val j hj];omega
    rw [PV_DL_EncoderFold.finite,PV_RunJoin_EncoderPairCell49.complete inst f hm ha q basis j hj]
    rw [ProverCommitNativePair48.range]
    trans (do let p ← mapResult (pairMap f) (ProverCommitNativePair48.step q basis j (p0,p1))
              PV_DL_EncoderFold.finite inst (amap f q) (amap f basis) n (PV_DL_EncoderRange.advance j) p.1 p.2)
    · apply congrArg (Aeneas.Std.bind _)
      funext p
      rcases p with ⟨a,b⟩
      rfl
    symm
    simpa only [PV_DL_EncoderRange.advance] using
      PV_RunJoin_WeightMap46.map_bind (pairMap f) (pairMap f)
        (ProverCommitNativePair48.step q basis j (p0,p1))
        (fun p => ProverCommitNativePair48.range q basis n (PV_DL_EncoderRange.advance j) p)
        (fun p => PV_DL_EncoderFold.finite inst (amap f q) (amap f basis) n (PV_DL_EncoderRange.advance j) p.1 p.2)
        (fun p => by rcases p with ⟨a,b⟩; exact (ih _ hr a b).symm)
#print axioms complete
end R1Z.PV_RunJoin_EncoderPairs49
