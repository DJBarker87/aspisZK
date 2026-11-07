import NLQ_MetadataFlags
set_option autoImplicit false
namespace NMB_Metadata
open NLF_RefCell NLF_SdkModel
/-- Metadata is indexed by account occurrence. Only data/lamport handles are
retained from the original SDK state; no equality of aliased flags is assumed. -/
def install (s : State) (records : Nat → Account) : State :=
 {s with accounts := fun a => {records a with
   data := (s.accounts a).data, lamports := (s.accounts a).lamports}}
def reply {E A : Type} (records : Nat → Account) (out : State × Except E A) :=
 (install out.1 records,out.2)
theorem put (s : State) (r : Nat → Account) (i : Nat) (c : Cell Payload) :
 install (NLF_SdkModel.put s i c) r = NLF_SdkModel.put (install s r) i c := rfl
theorem wrap (s : State) (r : Nat → Account) (i t : Nat) (k : Kind) :
 NLF_SdkModel.wrap (install s r) i t k = reply r (NLF_SdkModel.wrap s i t k) := by
 cases k <;> unfold NLF_SdkModel.wrap
 all_goals dsimp only [install,reply]
 all_goals split <;> simp_all [install,reply,NLF_SdkModel.put]
theorem deref (s : State) (r : Nat → Account) (g : Guard) :
 NLF_SdkModel.deref (install s r) g = NLF_SdkModel.deref s g := rfl
theorem release (s : State) (r : Nat → Account) (g : Guard) :
 NLF_SdkModel.release (install s r) g =
 (NLF_SdkModel.release s g).map (fun post => install post r) := by
 unfold NLF_SdkModel.release
 dsimp only [install]
 split <;> rfl
#print wrap
#print release
#print axioms put
#print axioms wrap
#print axioms deref
#print axioms release
end NMB_Metadata
