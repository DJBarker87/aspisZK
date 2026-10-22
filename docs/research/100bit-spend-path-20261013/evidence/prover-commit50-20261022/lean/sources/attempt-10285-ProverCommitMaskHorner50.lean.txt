import AspisR1ProducerRelease47.MaskHorner50
import R1Z.ProverCommitPrepared50
import R1Z.ProverCommitHornerMath50
import R1Z.ProverCommitQArray48
import R1Z.ProverCommitBasisCounter47
/-! Complete degree-26 prepared Horner value for arbitrary canonical input
coefficients. Their selected-mask provenance is a separate producer obligation. -/
set_option autoImplicit false
namespace R1Z.ProverCommitMaskHorner50
open Aeneas Aeneas.Std Result AspisR1ProducerRelease47
open ProverCommitPrimitive47 ProverCommitSubfieldOps47
open AspisR1.ExtractedCurrentQM31Exact (decode QM31Exact)
attribute [local irreducible] ProverCommitQArray48.array ProverCommitNativeQ48.source ProverCommitInterpolationPoly48.poly

theorem go (q : Nat → Old.Q) (hq : ∀ i, i<27 → Canonical (q i)) (x : QM31Exact)
    (a : Nat → Nat → U32)
    (ha : ∀ i j : Fin 3, ((a i.val j.val).val : AspisV8R15.ExactTowerBase.M31Exact)=
      ProverCommitChannelAlgebra49.components x i j)
    (n : Nat) (left : U8) (hl : left.val=n) (hn : n≤27)
    (acc : Old.Q) (hacc : Canonical acc) :
    ∃ z : Old.Q, mask_horner50.go (ProverCommitQArray48.array 27#usize q)
      (ProverCommitPrepared50.matrix a) left (ProverCommitNativeQ48.source acc)=ok (ProverCommitNativeQ48.source z) ∧
      Canonical z ∧ decode z=decode acc*x^n+(ProverCommitInterpolationPoly48.poly n (fun i => decode (q i))).eval x := by
  induction n generalizing left acc with
  | zero =>
    have hz : left=0#u8 := by scalar_tac
    refine ⟨acc,?_,hacc,?_⟩
    · rw [mask_horner50.go,hz];rfl
    · simp only [pow_zero,mul_one,ProverCommitInterpolationPoly48.poly,
        Finset.range_zero,Finset.sum_empty,Polynomial.eval_zero,add_zero]
  | succ n ih =>
    have hz : left≠0#u8 := by scalar_tac
    have hdec : (U8.wrapping_sub left 1#u8).val=n := by
      rw [ProverCommitBasisCounter47.sub_one left (by omega)];omega
    let idx := core.convert.num.FromUsizeU8.from (U8.wrapping_sub left 1#u8)
    have hidx : idx.val=n := by scalar_tac
    obtain ⟨p,hp,hcp,hdp⟩ := ProverCommitPrepared50.mul a x acc hacc ha
    obtain ⟨next,hnext,hcnext,hdnext⟩ := ProverCommitNativeQ48.add p (q n) hcp (hq _ (by omega))
    obtain ⟨z,hz0,hcz,hdz⟩ := ih _ hdec (by omega) next hcnext
    refine ⟨z,?_,hcz,?_⟩
    · rw [mask_horner50.go]
      simp only [hz,if_false,lift,bind_tc_ok,hp]
      rw [ProverCommitQArray48.index 27#usize q idx (by change idx.val<27;rw [hidx];omega)]
      simp only [bind_tc_ok]
      rw [hidx,hnext]
      exact hz0
    · rw [hdz,hdnext,hdp,ProverCommitHornerMath50.eval_succ,pow_succ]
      ring

theorem exact_result (q : Nat → Old.Q) (hq : ∀ i, i<27 → Canonical (q i))
    (x : Old.Q) (hx : Canonical x) :
    ∃ z : Old.Q, mask_horner50.eval (ProverCommitQArray48.array 27#usize q) (ProverCommitNativeQ48.source x)=
      ok (ProverCommitNativeQ48.source z) ∧ Canonical z ∧
      decode z=(ProverCommitInterpolationPoly48.poly 27 (fun i => decode (q i))).eval (decode x) := by
  obtain ⟨a,ha,hca,hva⟩ := ProverCommitPrepared50.prepare x hx
  obtain ⟨z,hz,hcz,hdz⟩ := go q hq (decode x) a hva 26 26#u8 rfl (by decide) (q 26) (hq _ (by decide))
  refine ⟨z,?_,hcz,?_⟩
  · rw [mask_horner50.eval,ha]
    simp only [bind_tc_ok]
    rw [ProverCommitQArray48.index 27#usize q 26#usize (by decide)]
    exact hz
  · rw [hdz]
    exact ProverCommitHornerMath50.top (fun i => decode (q i)) (decode x) 26

#print axioms go
#print axioms exact_result
end R1Z.ProverCommitMaskHorner50
