import R1Z.ProverCommitRoundStep48
import R1Z.PV_RunJoin_FourChildren44
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_RoundStepValue44
open Aeneas Aeneas.Std Result ProverRwFull
open ProverCommitWideOps48 ProverCommitMix48 PV_RunJoin_WideArithmetic44
open ProverCommitRoundStep48 (perm permutation)
open PV_RunJoin_FoldCell44 (array)
variable [ExternalTypes]
attribute [local irreducible] sourceArray source value

theorem step (ops : ExternalFuns) (count : Usize) (q w xs : Nat → Raw) (hq : ∀ k, k < 1024 → canonical (q k))
    (hw : ∀ k, k < 1024 → canonical (w k)) (hxs : ∀ k, k < 7 → canonical (xs k))
    (d s t : Usize) (hd : d.val < 256) (size : 4*d.val + 4 ≤ count.val) (hs : s.val < 4) (ht : t.val < 4) :
    ∃ ys : Nat → Raw,
      @ProverRwFull.prover.round_loop0_loop0_loop0.body _ (ProverRwP6BodyCandidate.selected ops)
        (Array.to_slice (array count q)) (Array.to_slice (array count w)) d s (array 7#usize xs) t=
        ok (.cont (array 7#usize ys,Usize.wrapping_add t 1#usize)) ∧
      (∀ k, k < 7 → canonical (ys k)) ∧
      ∀ k, k < 7 → value (ys k)=value (xs k)+
        if k=s.val+perm t.val then value (q (4*d.val+s.val))*value (w (4*d.val+t.val)) else 0 := by
  have seven : (7#usize).val=7 := rfl
  have big : (1024#usize).val=1024 := rfl
  obtain ⟨p,hp,hpv,hpb⟩ := permutation t ht
  have hidx : (Usize.wrapping_add s p).val=s.val+p.val :=
    ProverCommitBasisFillValue47.add_val s p (by omega)
  have hqidx := ProverCommitFoldRange48.offset_val d hd s (by omega)
  have hwidx := ProverCommitFoldRange48.offset_val d hd t (by omega)
  obtain ⟨m,hm,hcm,hdm⟩ := mul_exact (q (4*d.val+s.val)) (w (4*d.val+t.val))
    (hq _ (by omega)) (hw _ (by omega))
  obtain ⟨z,hz,hcz,hdz⟩ := add_exact (xs (s.val+p.val)) m (hxs _ (by omega)) hcm
  let ys := Function.update xs (s.val+p.val) z
  refine ⟨ys,?_,?_,?_⟩
  · unfold ProverRwFull.prover.round_loop0_loop0_loop0.body
    simp only [show t < 4#usize from ht,↓reduceIte,ProverRwFull.weights.PERM,hp,bind_tc_ok,lift]
    unfold array
    rw [ProverCommitArray49.index 7#usize _ _ (by rw [hidx];omega)]
    rw [PV_RunJoin_Vector44.read count _ _ (by rw [hqidx];omega),
      PV_RunJoin_Vector44.read count _ _ (by rw [hwidx];omega)]
    simp only [hidx,hqidx,hwidx,bind_tc_ok,
      PV_RunJoin_WideArithmetic44.mul ops _ _ _ hm,
      PV_RunJoin_WideArithmetic44.add ops _ _ _ hz]
    rw [ProverCommitArray49.update 7#usize _ _ (by rw [hidx];omega)]
    simp only [hidx,bind_tc_ok]
    congr 2
    apply congrArg (ProverCommitArray49.array 7#usize)
    funext k
    by_cases h : k = s.val+p.val
    · subst k;simp only [ys,Function.update_self]
    · simp only [ys,Function.update_of_ne h]
  · intro k hk
    by_cases h : k=s.val+p.val
    · subst k;simp only [ys,Function.update_self];exact hcz
    · simp only [ys,Function.update_of_ne h];exact hxs k hk
  · intro k hk
    by_cases h : k=s.val+p.val
    · subst k
      simp only [ys,Function.update_self,hdz,hdm,hpv,if_true]
    · have h' : k≠s.val+perm t.val := by rwa [← hpv]
      simp only [ys,Function.update_of_ne h,if_neg h',add_zero]

#print axioms step
end R1Z.PV_RunJoin_RoundStepValue44
