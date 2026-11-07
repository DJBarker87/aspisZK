import NMB_Metadata
set_option autoImplicit false
namespace NMB_MetadataBorrow
open NLF_RefCell NLF_SdkModel NMB_Metadata
theorem try_borrow_data (s : State) (r : Nat → Account) (a t : Nat) :
 NLF_SdkModel.try_borrow_data (install s r) a t =
 reply r (NLF_SdkModel.try_borrow_data s a t) :=
 NMB_Metadata.wrap s r (s.accounts a).data t .shared
#print axioms try_borrow_data
theorem try_borrow_mut_data (s : State) (r : Nat → Account) (a t : Nat) :
 NLF_SdkModel.try_borrow_mut_data (install s r) a t =
 reply r (NLF_SdkModel.try_borrow_mut_data s a t) :=
 NMB_Metadata.wrap s r (s.accounts a).data t .exclusive
#print axioms try_borrow_mut_data
theorem try_borrow_lamports (s : State) (r : Nat → Account) (a t : Nat) :
 NLF_SdkModel.try_borrow_lamports (install s r) a t =
 reply r (NLF_SdkModel.try_borrow_lamports s a t) :=
 NMB_Metadata.wrap s r (s.accounts a).lamports t .shared
#print axioms try_borrow_lamports
theorem try_borrow_mut_lamports (s : State) (r : Nat → Account) (a t : Nat) :
 NLF_SdkModel.try_borrow_mut_lamports (install s r) a t =
 reply r (NLF_SdkModel.try_borrow_mut_lamports s a t) :=
 NMB_Metadata.wrap s r (s.accounts a).lamports t .exclusive
#print axioms try_borrow_mut_lamports
end NMB_MetadataBorrow
