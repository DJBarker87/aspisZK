import R1Z.ProverCommitSuccessorPoint49
/-! Complete three-point owner equals source/model semantic statement points,
including both toggles and the complete successor carry loop. -/
set_option autoImplicit false
noncomputable section
namespace R1Z.ProverCommitStatementPoints49
open Aeneas Aeneas.Std Result AspisR1ProducerRelease47
open ProverCommitPrimitive47 ProverCommitSubfieldOps47
open ProverCommitSubtraction47 (one one_canonical one_decode)
open AspisR1.ExtractedCurrentQM31Exact (decode QM31Exact)
open ProverCommitSuccessorPoint49
open R0P.SemSource

attribute [local irreducible] ProverCommitQArray48.array ProverCommitNativeQ48.source

theorem absorption_exact (p : Nat → Old.Q) (hp : ∀ k, k<10 → Canonical (p k)) :
    ∃ z : Nat → Old.Q, points.absorption (ProverCommitQArray48.array 10#usize p)=
      ok (ProverCommitQArray48.array 10#usize z) ∧
      (∀ k, k<10 → Canonical (z k)) ∧ decoded z=xor12Point (decoded p) := by
  obtain ⟨p7,h7,hc7,hd7⟩ := ProverCommitNativeQ48.sub one (p 7) one_canonical (hp _ (by omega))
  obtain ⟨p6,h6,hc6,hd6⟩ := ProverCommitNativeQ48.sub one (p 6) one_canonical (hp _ (by omega))
  let z := Function.update (Function.update p 7 p7) 6 p6
  refine ⟨z,?_,?_,?_⟩
  · rw [points.absorption,ProverCommitQArray48.index 10#usize p 7#usize (by decide)]
    simp only [ProverCommitSampleTail49.source_one,show (7#usize).val=7 from rfl,h7,bind_tc_ok]
    rw [ProverCommitQArray48.update 10#usize p 7#usize (by decide)]
    simp only [bind_tc_ok,show (7#usize).val=7 from rfl]
    rw [ProverCommitQArray48.index 10#usize _ 6#usize (by decide)]
    simp only [show (6#usize).val=6 from rfl,Function.update_of_ne (by decide : (6:Nat)≠7),h6,bind_tc_ok]
    exact ProverCommitQArray48.update 10#usize _ 6#usize (by decide) p6
  · intro k hk
    by_cases h6 : k=6
    · subst k;simpa only [z,Function.update_self] using hc6
    · by_cases h7 : k=7
      · subst k;simpa only [z,Function.update_of_ne (by decide : (7:Nat)≠6),Function.update_self] using hc7
      · simpa only [z,Function.update_of_ne h6,Function.update_of_ne h7] using hp k hk
  · funext k
    change decode (z k.val)=_
    unfold xor12Point
    by_cases h6 : k.val=6
    · rw [if_pos (Or.inr h6)]
      simp only [z,h6,Function.update_self,hd6,one_decode,decoded]
    · by_cases h7 : k.val=7
      · rw [if_pos (Or.inl h7)]
        simp only [z,h7,Function.update_of_ne (by decide : (7:Nat)≠6),Function.update_self,hd7,one_decode,decoded]
      · rw [if_neg (by tauto)]
        simp only [z,Function.update_of_ne h6,Function.update_of_ne h7,decoded]

theorem points_exact (p : Nat → Old.Q) (hp : ∀ k, k<10 → Canonical (p k)) :
    ∃ s a : Nat → Old.Q,
      points.all (ProverCommitQArray48.array 10#usize p)=ok (Array.make 3#usize
        [ProverCommitQArray48.array 10#usize p,ProverCommitQArray48.array 10#usize s,
         ProverCommitQArray48.array 10#usize a]) ∧
      (∀ k, k<10 → Canonical (s k)) ∧ (∀ k, k<10 → Canonical (a k)) ∧
      ∀ i : Fin 3, toR0 (decoded (![p,s,a] i))=openingPoints (decoded p) i := by
  obtain ⟨s,hs,hcs,hds⟩ := successor_exact p hp
  obtain ⟨a,ha,hca,hda⟩ := absorption_exact p hp
  refine ⟨s,a,?_,hcs,hca,?_⟩
  · simp only [points.all,hs,ha,bind_tc_ok]
  · intro i
    fin_cases i
    · rfl
    · change toR0 (decoded s)=toR0 (successorPoint (decoded p))
      rw [hds]
    · change toR0 (decoded a)=toR0 (xor12Point (decoded p))
      rw [hda]

#print axioms absorption_exact
#print axioms points_exact
end R1Z.ProverCommitStatementPoints49
