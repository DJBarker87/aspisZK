import NLQ_CopyTrace
set_option autoImplicit false
namespace NLQ_CopyCases
open NLF_RefCell NLF_SdkModel NLQ_CopyTrace
/-- Exact acquire-conflict prefix with no deref/copy/release suffix. -/
theorem conflict (s : State) (a t : Nat) (src : List UInt8)
 (bad : ¬ ((s.cells (s.accounts a).data).writer=none ∧ (s.cells (s.accounts a).data).readers=[])) :
 G s a t src = ⟨.returned s (.error .accountBorrowFailed),
  [.acquire s s a t (.error .accountBorrowFailed)]⟩ := by
 simp [G,try_borrow_mut_data,wrap,exclusive,bad]
/-- Exclusive admission is derived from THIS cell's current ledger; no guard
is supplied as an independent success premise. -/
theorem wrong_length (s : State) (a t : Nat) (src : List UInt8)
 (free : (s.cells (s.accounts a).data).writer=none)
 (empty : (s.cells (s.accounts a).data).readers=[])
 (bad : src.length≠(s.cells (s.accounts a).data).payload.bytes.length) :
 let held := put s (s.accounts a).data {s.cells (s.accounts a).data with writer:=some t}
 let g : Guard := ⟨(s.accounts a).data,t,.exclusive⟩
 G s a t src = ⟨.abort held,
  [.acquire s held a t (.ok g),.deref held g (deref held g),.abort held]⟩ := by
 dsimp only
 unfold G
 rw [NLF_ExclusiveBracket.exclusive_admission s a t free empty]
 simp only [exclusive_deref]
 simp [bad]
#check @conflict
#check @wrong_length
#print axioms conflict
#print axioms wrong_length
end NLQ_CopyCases
