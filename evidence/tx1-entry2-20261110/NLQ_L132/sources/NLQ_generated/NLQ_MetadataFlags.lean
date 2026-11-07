import NLQ_MetadataAdmission
set_option autoImplicit false
namespace NLQ_MetadataFlags
open NLF_RefCell NLF_SdkModel
/-- Per-account metadata, without changing a cell identity, payload or token.
This supports a carrier generalization; it is not an entrypoint ABI claim. -/
def flags (s : State) (f : Nat → Bool) : State :=
 {s with accounts:=fun a=>{s.accounts a with writable:=f a}}
def reply {E A : Type} (f : Nat → Bool) (out : State × Except E A) :=
 (flags out.1 f,out.2)
theorem put (s : State) (f : Nat → Bool) (i : Nat) (c : Cell Payload) :
 flags (NLF_SdkModel.put s i c) f=NLF_SdkModel.put (flags s f) i c := rfl
/-- Both returning and conflict outcomes commute with the metadata map. -/
theorem wrap (s : State) (f : Nat → Bool) (i t : Nat) (k : Kind) :
 NLF_SdkModel.wrap (flags s f) i t k=reply f (NLF_SdkModel.wrap s i t k) := by
 cases k <;> unfold NLF_SdkModel.wrap
 all_goals dsimp only [flags,reply]
 all_goals split <;> simp_all [flags,reply,NLF_SdkModel.put]
theorem deref (s : State) (f : Nat → Bool) (g : Guard) :
 NLF_SdkModel.deref (flags s f) g=NLF_SdkModel.deref s g := rfl
/-- A live guard is released at its SAME cell/token, with the same error. -/
theorem release (s : State) (f : Nat → Bool) (g : Guard) :
 NLF_SdkModel.release (flags s f) g=
 (NLF_SdkModel.release s g).map (fun post=>flags post f) := by
 unfold NLF_SdkModel.release
 dsimp only [flags]
 split <;> simp_all [flags,NLF_SdkModel.put]
#print wrap
#print release
#print axioms put
#print axioms wrap
#print axioms deref
#print axioms release
end NLQ_MetadataFlags
