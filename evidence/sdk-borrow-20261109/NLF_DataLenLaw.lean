import NLF_WrapperFlagLaws
set_option autoImplicit false
namespace NLF_DataLenLaw
open NLF_RefCell NLF_SdkModel NLF_WrapperFlagLaws
theorem result (s : State) (a t : Nat) (fresh : t∉(s.cells (s.accounts a).data).readers) :
    try_data_len s a t = if sharedAllowed s (s.accounts a).data then
      (s,.ok ((fun p => p.bytes.length) (s.cells (s.accounts a).data).payload)) else (s,.error .accountBorrowFailed) :=
  scalar_complete s _ t _ fresh

theorem panic_result (s : State) (a t : Nat) (fresh : t∉(s.cells (s.accounts a).data).readers) :
    data_len s a t = if sharedAllowed s (s.accounts a).data then
      some (s,((fun p => p.bytes.length) (s.cells (s.accounts a).data).payload)) else none := by
  unfold NLF_SdkModel.data_len
  rw [result s a t fresh]
  split_ifs <;> rfl
#print axioms result
#print axioms panic_result
end NLF_DataLenLaw
