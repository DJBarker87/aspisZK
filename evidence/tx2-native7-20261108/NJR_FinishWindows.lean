import NIG_FinishInput
set_option autoImplicit false
namespace NJR_FinishWindows
open Aeneas Aeneas.Std

/-- Raw word obligations at the three proof regions. This predicate is an
explicit missing history obligation, never a root hypothesis or a certificate. -/
def History (proof : Slice U8) : Prop :=
 (∀ i, i<7 → ∀ j, j<8 → NIG_FinishInput.word proof.val (7527+32*i+4*j)<2147483647) ∧
 (∀ i, i<7 → ∀ j, j<8 → NIG_FinishInput.word proof.val (7783+32*i+4*j)<2147483647) ∧
 (∀ i, i<64 → ∀ j, j<8 → NIG_FinishInput.word proof.val (8007+32*i+4*j)<2147483647)

theorem word_window (bytes : List U8) (lo n at : Nat) (inside : at+4≤n) :
 NIG_FinishInput.word ((bytes.drop lo).take n) at=
 NIG_FinishInput.word bytes (lo+at) := by
 unfold NIG_FinishInput.word
 simp only [List.getElem?_take, List.getElem?_drop]
 simp only [show at<n by omega,show at+1<n by omega,show at+2<n by omega,
  show at+3<n by omega,ite_true]
 congr 2 <;> congr 1 <;> omega

/-- Reusable window transport. No concrete proof numeral is normalized. -/
theorem windows (proof bytes : Slice U8) (lo n : Nat)
 (size : lo+32*n≤proof.val.length)
 (view : bytes.val=(proof.val.drop lo).take (32*n))
 (words : ∀ i, i<n → ∀ j, j<8 →
  NIG_FinishInput.word proof.val (lo+32*i+4*j)<2147483647) :
 NIG_FinishInput.Windows bytes n := by
 constructor
 · rw [view,List.length_take,List.length_drop]
   omega
 · intro i hi j hj
   rw [view,word_window _ lo (32*n) (32*i+4*j) (by omega)]
   simpa only [Nat.add_assoc] using words i hi j hj

/-- Precisely the raw-history component required at the ACTUAL finish View.
The history predicate is a named missing upstream lemma, not proof of it. -/
theorem three (proof r0 r1 final : Slice U8)
 (size : 10055≤proof.val.length)
 (r0view : r0.val=(proof.val.drop 7527).take 224)
 (r1view : r1.val=(proof.val.drop 7783).take 224)
 (fview : final.val=(proof.val.drop 8007).take 2048)
 (history : History proof) :
 NIG_FinishInput.Windows r0 7 ∧ NIG_FinishInput.Windows r1 7 ∧
 NIG_FinishInput.Windows final 64 := by
 exact ⟨windows proof r0 7527 7 (by omega) r0view history.1,
  windows proof r1 7783 7 (by omega) r1view history.2.1,
  windows proof final 8007 64 (by omega) fview history.2.2⟩

#print axioms word_window
#print axioms windows
#print axioms three
end NJR_FinishWindows
