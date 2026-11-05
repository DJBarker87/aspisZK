import NIQ_RawWindows
set_option autoImplicit false
namespace NIQ_FieldDomains
open Aeneas Aeneas.Std AspisR1 AspisR1Stage2

/-- Exact native weights::field envelope, expressed before decoding. -/
def Domain (bytes : Slice U8) (i : Nat) : Prop :=
 bytes.val.length <= 2048 ∧ i < 64 ∧ 32*(i+1) <= bytes.val.length ∧
 (NIQ_RawWindows.cell bytes i).length = 32 ∧
 ∀ j, j < 8 → NIG_FinishInput.word (NIQ_RawWindows.cell bytes i) (4*j) < 2147483647

theorem windows (bytes : Slice U8) (n i : Nat)
 (h : NIG_FinishInput.Windows bytes n) (cap : n <= 64) (small : i < n) :
 Domain bytes i := by
 refine ⟨?_, by omega, NIQ_RawWindows.range bytes n i h small,
  NIQ_RawWindows.length bytes n i h small, ?_⟩
 · rw [h.1]; omega
 · intro j hj
   exact NIQ_RawWindows.canonical bytes n i j h small hj

theorem final (proof : Slice U8) (v : verifier.View) (p : verifier.Prepared)
 (a : verifier.Accumulator) (h : NIG_FinishInput.Domain proof v p a)
 (i : Nat) (small : i < 64) : Domain v.final_message i :=
 windows v.final_message 64 i h.final_words (by omega) small

theorem round0 (proof : Slice U8) (v : verifier.View) (p : verifier.Prepared)
 (a : verifier.Accumulator) (h : NIG_FinishInput.Domain proof v p a)
 (i : Nat) (small : i < 7) : Domain v.round0 i :=
 windows v.round0 7 i h.round0_words (by omega) small

theorem round1 (proof : Slice U8) (v : verifier.View) (p : verifier.Prepared)
 (a : verifier.Accumulator) (h : NIG_FinishInput.Domain proof v p a)
 (i : Nat) (small : i < 7) : Domain v.round1 i :=
 windows v.round1 7 i h.round1_words (by omega) small

theorem backed_byte (proof bytes : Slice U8) (offset count i : Nat)
 (backed : bytes.val = (proof.val.drop offset).take count) (small : i < count) :
 bytes.val[i]? = proof.val[offset+i]? := by
 rw [backed, List.getElem?_take_of_lt small, List.getElem?_drop]

theorem final_byte (proof : Slice U8) (v : verifier.View) (p : verifier.Prepared)
 (a : verifier.Accumulator) (h : NIG_FinishInput.Domain proof v p a)
 (i j : Nat) (hi : i < 64) (hj : j < 32) :
 (NIQ_RawWindows.cell v.final_message i)[j]? = proof.val[8007+32*i+j]? := by
 rw [NIQ_RawWindows.byte v.final_message i j hj]
 rw [backed_byte proof v.final_message 8007 2048 (32*i+j) h.final (by omega)]
 simp only [Nat.add_assoc]

#print axioms windows
#print axioms final
#print axioms round0
#print axioms round1
#print axioms backed_byte
#print axioms final_byte
end NIQ_FieldDomains
