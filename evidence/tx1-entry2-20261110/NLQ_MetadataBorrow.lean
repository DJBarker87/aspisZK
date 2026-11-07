import NLQ_MetadataFlags
set_option autoImplicit false
namespace NLQ_MetadataBorrow
open NLF_RefCell NLF_SdkModel NLQ_MetadataFlags
/-- Same account occurrence and token: shared data borrowing is independent
of writable metadata, including every conflict and alias pre-state. -/
theorem shared (s : State) (f : Nat → Bool) (a t : Nat) :
 try_borrow_data (flags s f) a t=reply f (try_borrow_data s a t) :=
 NLQ_MetadataFlags.wrap s f (s.accounts a).data t .shared
/-- The SDK's RefCell exclusive-borrow operation itself has the same property;
program metadata validation remains a separate, earlier child occurrence. -/
theorem exclusive (s : State) (f : Nat → Bool) (a t : Nat) :
 try_borrow_mut_data (flags s f) a t=reply f (try_borrow_mut_data s a t) :=
 NLQ_MetadataFlags.wrap s f (s.accounts a).data t .exclusive
#print shared
#print exclusive
#print axioms shared
#print axioms exclusive
end NLQ_MetadataBorrow
