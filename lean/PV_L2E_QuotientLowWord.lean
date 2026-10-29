import PV_L2E_ArrayDigits
set_option autoImplicit false
namespace PV_L2E_QuotientLowWord
open PV_L2E_ArrayMemory PV_L2D_DivisionBounds PV_L2E_WordRank

/-- A small positional rank forces every higher array slot to zero. The
proof is symbolic in the array width; it never normalizes concrete digits. -/
theorem small_rank (a : Memory) (n : Nat) (small : rank (backwards a (n+1))<B) :
    rank (backwards a (n+1))=a 0 ∧ ∀ i,0<i → i<n+1 → a i=0 := by
  induction n with
  | zero =>
    simp only [backwards,rank,List.length_nil,pow_zero,Nat.mul_one,Nat.add_zero] at *
    exact ⟨rfl,by intros; omega⟩
  | succ n ih =>
    have he : rank (backwards a (n+2))=
        a (n+1)*B^(n+1)+rank (backwards a (n+1)) := by
      simp only [backwards,rank,length]
    have hp : B≤B^(n+1) := by
      rw [pow_succ]
      have hpos : 0<B^n := pow_pos (by decide : 0<B) n
      nlinarith
    have hz : a (n+1)=0 := by rw [he] at small; nlinarith
    have ht : rank (backwards a (n+1))<B := by rw [he,hz,Nat.zero_mul,Nat.zero_add] at small; exact small
    have hi := ih ht
    refine ⟨?_,?_⟩
    · rw [he,hz,Nat.zero_mul,Nat.zero_add,hi.1]
    · intro i hpos hcap
      by_cases heq : i=n+1
      · simpa [heq] using hz
      · exact hi.2 i hpos (by omega)

/-- The native helper returns quotient[0], not an abstract rank. This binds
that returned word and the debug-only high-zero assertions to the quotient
law already proved for all 256-bit inputs. -/
theorem after_eight (a : Memory) (small : ∀ i,i<8 → a i<B) :
    (PV_L2E_ArrayDigits.run 8 8 a).1 0≤256 ∧
    ∀ i,0<i → i<8 → (PV_L2E_ArrayDigits.run 8 8 a).1 i=0 := by
  have hc := PV_L2E_ArrayDigits.complete 8 8 a
  have hb := PV_L2E_DigitsValue.quotient_256 (backwards a 8) (length a 8) (bounds a 8 small)
  rw [←hc.1] at hb
  have hl : rank (backwards (PV_L2E_ArrayDigits.run 8 8 a).1 8)<B :=
    lt_of_le_of_lt hb (by decide : 256<B)
  have hs := small_rank (PV_L2E_ArrayDigits.run 8 8 a).1 7 hl
  exact ⟨by rw [←hs.1]; exact hb,hs.2⟩

#print axioms small_rank
#print axioms after_eight
end PV_L2E_QuotientLowWord
