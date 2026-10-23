import Std
set_option autoImplicit false
namespace AspisR1.S2A

/-- Three u8-offset native observation windows cover every prefix byte. -/
theorem prefix_window (i : Nat) (bound : i < 688) :
    ∃ w offset : Nat, w < 3 ∧ offset < 256 ∧ i = 256*w+offset := by
  refine ⟨i/256, i%256, ?_, ?_, ?_⟩ <;> omega

/-- Pointwise observations are universal over the SAME proof/candidate lists;
combining windows never chooses different input executions or candidates. -/
theorem prefix_from_windows {Byte : Type} (proof candidate : List Byte)
    (candidateLength : candidate.length = 688)
    (observed : ∀ w offset, w < 3 → offset < 256 → 256*w+offset < 688 →
      proof[256*w+offset]? = candidate[256*w+offset]?) :
    proof.take 688 = candidate := by
  apply List.ext_getElem?
  intro i
  by_cases bound : i < 688
  · rw [List.getElem?_take_of_lt bound]
    obtain ⟨w, offset, hw, ho, hi⟩ := prefix_window i bound
    subst i
    exact observed w offset hw ho bound
  · have cp : candidate[i]? = none := by simp [candidateLength]; omega
    have pp : (proof.take 688)[i]? = none := by simp; omega
    rw [cp, pp]

#print axioms prefix_window
#print axioms prefix_from_windows

/-- The isolated final176-byte interval is covered by two128-offset cuts. -/
theorem tail_window (i : Nat) (lower : 512 ≤ i) (upper : i < 688) :
    ∃ w offset : Nat, w < 2 ∧ offset < 128 ∧ i = 512+128*w+offset := by
  refine ⟨(i-512)/128, (i-512)%128, ?_, ?_, ?_⟩ <;> omega

/-- Assemble the four checked native contexts on one fixed pair of carriers.
The tail split changes observation selection only, not the execution inputs. -/
theorem prefix_from_split_windows {Byte : Type} (proof candidate : List Byte)
    (candidateLength : candidate.length = 688)
    (head : ∀ w offset, w < 2 → offset < 256 →
      proof[256*w+offset]? = candidate[256*w+offset]?)
    (tail : ∀ w offset, w < 2 → offset < 128 → 512+128*w+offset < 688 →
      proof[512+128*w+offset]? = candidate[512+128*w+offset]?) :
    proof.take 688 = candidate := by
  apply prefix_from_windows proof candidate candidateLength
  intro w offset hw ho bound
  by_cases first : w < 2
  · exact head w offset first ho
  · have last : w = 2 := by omega
    subst w
    obtain ⟨t, o, ht, hto, same⟩ := tail_window (256*2+offset) (by omega) bound
    rw [same]
    exact tail t o ht hto (by omega)

#print axioms tail_window
#print axioms prefix_from_split_windows
end AspisR1.S2A
