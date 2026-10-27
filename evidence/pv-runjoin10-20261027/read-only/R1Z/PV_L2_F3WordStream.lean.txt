import R1Z.PV_L2_F3WordCarrier

/-! Adaptive permutations on full u32 streams, including discarded high bits.
This is the ACTUAL Word carrier, not an independent successful-mask draw. -/
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_L2_F3WordStream
open R1Z.PV_L2_F3Words R1Z.PV_L2_F3Adaptive R1Z.PV_L2_F3WordCarrier
  R1Z.CommitReadsR1 R1Z.CouplingR1PBin
attribute [local instance] Classical.propDecidable

/-- Reorganize words without loss: candidate stream plus untouched high bits. -/
def splitStream (n : Nat) : (Fin n → Word) ≃ (Fin n → Fin 2) × (Fin n → Candidate) where
  toFun w := (fun i => (splitWord (w i)).1, fun i => (splitWord (w i)).2)
  invFun w i := splitWord.symm (w.1 i,w.2 i)
  left_inv w := by funext i; exact splitWord.symm_apply_apply (w i)
  right_inv w := by
    apply Prod.ext <;> funext i
    · exact congrArg Prod.fst (splitWord.apply_symm_apply (w.1 i,w.2 i))
    · exact congrArg Prod.snd (splitWord.apply_symm_apply (w.1 i,w.2 i))

def wordStreamEquiv (e : Relabel) (n index : Nat) : (Fin n → Word) ≃ (Fin n → Word) :=
  (splitStream n).trans ((Equiv.prodCongr (Equiv.refl (Fin n → Fin 2))
    (streamEquiv e n index)).trans (splitStream n).symm)

theorem split_stream_permute (e : Relabel) (n index : Nat) (w : Fin n → Word) :
    splitStream n (wordStreamEquiv e n index w) =
      ((splitStream n w).1,streamEquiv e n index (splitStream n w).2) := by
  simp only [wordStreamEquiv,Equiv.trans_apply,Equiv.apply_symm_apply,Equiv.prodCongr_apply]
  rfl

theorem high_bits_preserved (e : Relabel) (n index : Nat) (w : Fin n → Word) :
    (fun i => (wordStreamEquiv e n index w i).val / 2147483648) =
      (fun i => (w i).val / 2147483648) := by
  exact congrArg (fun p : (Fin n → Fin 2) × (Fin n → Candidate) => fun i => (p.1 i).val)
    (split_stream_permute e n index w)

theorem rejection_history_preserved (e : Relabel) (n index : Nat) (w : Fin n → Word) :
    (fun i => rejB (wordStreamEquiv e n index w i)) = (fun i => rejB (w i)) := by
  have hc := acceptance_history e n index (splitStream n w).2
  have hs := congrArg Prod.snd (split_stream_permute e n index w)
  funext i
  have hci := congrFun hc i
  have hsi := congrFun hs i
  apply Bool.eq_iff_iff.mpr
  rw [rejB_iff,rejB_iff]
  change ((splitStream n (wordStreamEquiv e n index w)).2 i).val = 2147483647 ↔
    ((splitStream n w).2 i).val = 2147483647
  rw [hsi]
  have ha := ((splitStream n w).2 i).isLt
  have hb := (streamEquiv e n index (splitStream n w).2 i).isLt
  have hi : accepts (streamEquiv e n index (splitStream n w).2 i) ↔
      accepts ((splitStream n w).2 i) := by
    exact decide_eq_decide.mp hci
  unfold accepts at hi
  dsimp only
  omega

theorem actual_word_uniform (e : Relabel) (n index : Nat) (test : (Fin n → Word) → ℚ) :
    R0Z.mean (fun w => test (wordStreamEquiv e n index w)) = R0Z.mean test :=
  mp_equiv (wordStreamEquiv e n index) test

#print axioms splitStream
#print axioms split_stream_permute
#print axioms high_bits_preserved
#print axioms rejection_history_preserved
#print axioms actual_word_uniform
end R1Z.PV_L2_F3WordStream
