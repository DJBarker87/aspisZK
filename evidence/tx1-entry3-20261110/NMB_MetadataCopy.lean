import NMB_MetadataBorrow
import NLQ_CopyTrace
set_option autoImplicit false
namespace NMB_MetadataCopy
open NLF_RefCell NLF_SdkModel NMB_Metadata
/-- Full copy outcome, including the exact live-token abort state. -/
def outcome (r : Nat → Account) : NLF_CopyStep.Outcome → NLF_CopyStep.Outcome
 | .returned s v => .returned (install s r) v
 | .abort s => .abort (install s r)
theorem write (s : State) (r : Nat → Account) (g : Guard) (p : Payload) :
 NLF_ViewLaws.write (install s r) g p = install (NLF_ViewLaws.write s g p) r := rfl
theorem copy (s : State) (r : Nat → Account) (a t : Nat) (src : List UInt8) :
 NLF_CopyStep.run (install s r) a t src = outcome r (NLF_CopyStep.run s a t src) := by
 unfold NLF_CopyStep.run
 rw [NMB_MetadataBorrow.try_borrow_mut_data]
 cases h : try_borrow_mut_data s a t with
 | mk post v =>
  cases v with
  | error e => rfl
  | ok g =>
   dsimp only [reply]
   rw [NMB_Metadata.deref]
   split
   · rw [write,NMB_Metadata.release]
     cases hr : NLF_SdkModel.release (NLF_ViewLaws.write post g {NLF_SdkModel.deref post g with bytes := (NLF_CopyValue.copy src (NLF_SdkModel.deref post g).bytes 0 src.length)}) g <;> rfl
   · rfl
#print copy
#print axioms write
#print axioms copy
end NMB_MetadataCopy
