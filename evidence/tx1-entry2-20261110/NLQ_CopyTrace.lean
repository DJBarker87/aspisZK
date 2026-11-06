import NLF_SdkBorrowLaw
set_option autoImplicit false
namespace NLQ_CopyTrace
open NLF_RefCell NLF_SdkModel
/-- One complete state chain for the source copy bracket; every guard operation
is an explicit event on the SAME cell/token. No whole-buffer native unwind. -/
inductive Event where
 | acquire (before after : State) (account token : Nat) (reply : Except ProgramError Guard)
 | deref (state : State) (guard : Guard) (payload : Payload)
 | copy (before after : State) (guard : Guard) (source : List UInt8)
 | release (before : State) (guard : Guard) (reply : Except Error State)
 | abort (state : State)
structure Run where
 outcome : NLF_CopyStep.Outcome
 events : List Event

def G (s : State) (a t : Nat) (src : List UInt8) : Run :=
 let acquisition := try_borrow_mut_data s a t
 let first := Event.acquire s acquisition.1 a t acquisition.2
 match acquisition.2 with
 | .error e => ⟨.returned acquisition.1 (.error e),[first]⟩
 | .ok g =>
   let p := deref acquisition.1 g
   let prefix := [first,Event.deref acquisition.1 g p]
   if src.length=p.bytes.length then
     let v := {p with bytes:=NLF_CopyValue.copy src p.bytes 0 src.length}
     let written := NLF_ViewLaws.write acquisition.1 g v
     let release := NLF_SdkModel.release written g
     let events := prefix++[.copy acquisition.1 written g src,.release written g release]
     match release with
     | .ok post => ⟨.returned post (.ok ()),events⟩
     | .error _ => ⟨.abort acquisition.1,events++[.abort acquisition.1]⟩
   else ⟨.abort acquisition.1,prefix++[.abort acquisition.1]⟩
/-- Full outcome erasure: returning borrow errors and live-guard aborts, not
only successful copies. Native association still uses NLF K044/K045 windows. -/
theorem erasure (s : State) (a t : Nat) (src : List UInt8) :
 (G s a t src).outcome = NLF_CopyStep.run s a t src := by
 unfold G NLF_CopyStep.run
 cases h : try_borrow_mut_data s a t with
 | mk post reply =>
   cases reply with
   | error e => rfl
   | ok g =>
     dsimp only
     split
     · split <;> rfl
     · rfl
#check @erasure
#print axioms erasure
end NLQ_CopyTrace
