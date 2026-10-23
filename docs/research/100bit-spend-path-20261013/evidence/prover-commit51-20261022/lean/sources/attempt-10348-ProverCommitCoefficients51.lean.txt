import AspisR1ProducerRelease47.Coefficients51
import R1Z.ProverCommitInactiveModel49
import R1Z.ProverCommitQArray48
/-! Complete owned coefficient permutation, using the retained exact row owner. -/
set_option autoImplicit false
namespace R1Z.ProverCommitCoefficients51
open Aeneas Aeneas.Std Result AspisR1ProducerRelease47
open ProverCommitPrimitive47 ProverCommitSubfieldOps47
open AspisR1.ExtractedCurrentQM31Exact (decode QM31Exact)
attribute [local irreducible] ProverCommitNativeQ48.source ProverCommitQArray48.array

theorem cell (p : Nat → Old.Q) (j : Usize) :
    coefficients51.cell (ProverCommitQArray48.array 1024#usize p) j=
      ok (ProverCommitNativeQ48.source (p (AspisR1.rowNat j.val))) := by
  obtain ⟨r,hr,hvr⟩ := ProverCommitInactiveRow49.row_exact j
  rw [coefficients51.cell,hr]
  simp only [bind_tc_ok]
  rw [ProverCommitQArray48.index _ _ r (by rw [hvr];exact AspisR1.rowNat_lt j.val),hvr]

theorem go (p : Nat → Old.Q) (hp : ∀ i, i<1024 → Canonical (p i))
    (n : Nat) (left : U16) (hl : left.val=n) (hn : n≤1024)
    (q : Nat → Old.Q) (hq : ∀ k, k<1024 → Canonical (q k)) :
    ∃ z : Nat → Old.Q,
      coefficients51.go (ProverCommitQArray48.array 1024#usize p) left
        (ProverCommitQArray48.array 1024#usize q)=ok (ProverCommitQArray48.array 1024#usize z) ∧
      (∀ k, k<1024 → Canonical (z k)) ∧
      ∀ k, k<1024 → decode (z k)=if 1024 - n ≤ k then decode (p (AspisR1.rowNat k)) else decode (q k) := by
  induction n generalizing left q with
  | zero =>
    have hz : left=0#u16 := by scalar_tac
    refine ⟨q,?_,hq,?_⟩
    · rw [coefficients51.go,hz];rfl
    · intro k hk;rw [if_neg (by omega)]
  | succ n ih =>
    have hne : left≠0#u16 := by scalar_tac
    let i := U16.wrapping_sub 1024#u16 left
    have hi : i.val=1024-(n+1) := by
      dsimp only [i]
      rw [U16.wrapping_sub_val_eq]
      have hs : UScalar.size .U16=65536 := by rw [UScalar.size_def];decide
      rw [hs]
      change (1024+(65536-left.val))%65536=1024-(n+1)
      rw [hl];omega
    have hib : i.val<1024 := by omega
    have hdec : (U16.wrapping_sub left 1#u16).val=n := by
      rw [ProverCommitPairCounter47.sub_one left (by omega)];omega
    let idx := UScalar.cast .Usize i
    have hidx : idx.val=i.val := by scalar_tac
    let v := p (AspisR1.rowNat i.val)
    have hcv : Canonical v := hp _ (AspisR1.rowNat_lt _)
    let next := Function.update q i.val v
    have hcnext : ∀ k, k<1024 → Canonical (next k) := by
      intro k hk
      dsimp only [next]
      by_cases h : k=i.val
      · subst k;rw [Function.update_self];exact hcv
      · rw [Function.update_of_ne h];exact hq k hk
    obtain ⟨z,hz,hcz,hdz⟩ := ih _ hdec (by omega) next hcnext
    refine ⟨z,?_,hcz,?_⟩
    · rw [coefficients51.go]
      simp only [hne,if_false,lift,bind_tc_ok]
      change (do
        let cell ← coefficients51.cell (ProverCommitQArray48.array 1024#usize p) idx
        let out ← Array.update (ProverCommitQArray48.array 1024#usize q) idx cell
        coefficients51.go (ProverCommitQArray48.array 1024#usize p) (U16.wrapping_sub left 1#u16) out)=_
      rw [cell]
      simp only [bind_tc_ok,hidx]
      rw [ProverCommitQArray48.update _ _ idx (by rw [hidx];exact hib),hidx]
      exact hz
    · intro k hk
      rw [hdz k hk]
      by_cases htail : 1024 - n ≤ k
      · rw [if_pos htail,if_pos (by omega)]
      · rw [if_neg htail]
        by_cases hstart : k=i.val
        · rw [hstart,if_pos (by omega)]
          dsimp only [next]
          rw [Function.update_self]
        · have hbefore : ¬1024-(n+1)≤k := by omega
          rw [if_neg hbefore]
          exact congrArg decode (Function.update_of_ne hstart _ _)

theorem exact_result (p : Nat → Old.Q) (hp : ∀ i, i<1024 → Canonical (p i)) :
    ∃ z : Nat → Old.Q,
      coefficients51.eval (ProverCommitQArray48.array 1024#usize p)=ok (ProverCommitQArray48.array 1024#usize z) ∧
      (∀ k, k<1024 → Canonical (z k)) ∧
      ∀ k, k<1024 → decode (z k)=decode (p (AspisR1.rowNat k)) := by
  obtain ⟨z,hz,hcz,hdz⟩ := go p hp 1024 1024#u16 rfl (by decide)
    (fun _ => zero) (fun _ _ => zero_canonical)
  refine ⟨z,?_,hcz,?_⟩
  · rw [coefficients51.eval,ProverCommitQArray48.repeat_zero]
    exact hz
  · intro k hk
    simpa only [Nat.sub_self,Nat.zero_le,if_true] using hdz k hk

#print axioms cell
#print axioms go
#print axioms exact_result
end R1Z.ProverCommitCoefficients51
