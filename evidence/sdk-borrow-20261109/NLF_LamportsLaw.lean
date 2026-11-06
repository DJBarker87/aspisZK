import NLF_WrapperFlagLaws
set_option autoImplicit false
namespace NLF_LamportsLaw
open NLF_RefCell NLF_SdkModel NLF_WrapperFlagLaws
theorem result (s : State) (a t : Nat) (fresh : t∉(s.cells (s.accounts a).lamports).readers) :
    try_lamports s a t = if sharedAllowed s (s.accounts a).lamports then
      (s,.ok (Payload.money (s.cells (s.accounts a).lamports).payload)) else (s,.error .accountBorrowFailed) :=
  scalar_complete s _ t _ fresh

theorem panic_result (s : State) (a t : Nat) (fresh : t∉(s.cells (s.accounts a).lamports).readers) :
    lamports s a t = if sharedAllowed s (s.accounts a).lamports then
      some (s,(Payload.money (s.cells (s.accounts a).lamports).payload)) else none := by
  unfold NLF_SdkModel.lamports
  rw [result s a t fresh]
  split_ifs <;> rfl
#print axioms result
#print axioms panic_result
end NLF_LamportsLaw
