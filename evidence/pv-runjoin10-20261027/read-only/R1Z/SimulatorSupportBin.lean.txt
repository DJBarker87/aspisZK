import R1Z.SimulatorR1

/-! Finite-law support transport, used to carry the binary R-wire log from
honest views to ZF2's explicit simulator without an additional wire axiom. -/
set_option autoImplicit false
noncomputable section
namespace R1Z.SimulatorSupportBin
open R0Z

/-- Every output of an equal-law finite sampler is an output of the other.
This transports existence only; it does not change the simulator algorithm. -/
theorem equalLaws_output {R T V : Type} [Fintype R] [Fintype T]
    (f : R → V) (g : T → V) (h : EqualLaws f g) (t : T) :
    ∃ r, f r = g t := by
  classical
  by_contra hn
  have hf : ∀ r, f r ≠ g t := by simpa using hn
  have hz : law f (g t) = 0 := by
    simp [law, mean, hf]
  haveI : Nonempty T := ⟨t⟩
  have hp : 0 < law g (g t) := by
    unfold law mean
    apply div_pos _ (by exact_mod_cast Fintype.card_pos)
    have hb : (1 : ℚ) ≤ ∑ s : T, if g s = g t then (1 : ℚ) else 0 := by
      simpa using (Finset.single_le_sum
        (f := fun s : T => if g s = g t then (1 : ℚ) else 0)
        (fun s _ => by split_ifs <;> norm_num) (Finset.mem_univ t))
    exact lt_of_lt_of_le (by norm_num) hb
  rw [← h (g t), hz] at hp
  exact (lt_irrefl 0) hp

#print axioms equalLaws_output
end R1Z.SimulatorSupportBin
