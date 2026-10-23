import S2W_WrapperLaws
import S2X_RuntimeRetention

/-! Entry/write/history composition at the interpreted heap boundary. The
ledger version premise is the existing one, applied to the computed write
and actual entry payload, with no savedAtWrite or independent cut equality.
This does not identify the native Rust wrapper's allocation/copy operation
with the Heap interpreter; that source port remains separate. -/
set_option autoImplicit false
namespace AspisR1.S2W_EntryWriteHistory
open S2Trust S2W_TrustedStd S2W_WrapperLaws AdapterRw
open AspisV8R19.DuplexFrames

def payloadBytes (encode : UInt8 → Byte) (p : Payload) (n : Nat) : Bytes :=
  List.ofFn (fun i : Fin n => encode (p.contents i.val))

/-- Pointwise wrapper bytes lift to the SAME serialized checkpoint. -/
theorem written_bytes {F : Type} (encode : UInt8 → Byte)
    (s : Heap F) (a t o : Nat) (src : Payload)
    (empty : s.guards = []) (zero : s.counter (s.accounts a).1 = 0)
    (length : (s.payload (s.accounts a).1).descriptor.length = 1768) :
    payloadBytes encode ((writeBracket s a t o src).payload (s.accounts a).1) 1768 =
      payloadBytes encode src 1768 := by
  apply congrArg List.ofFn
  funext i
  exact congrArg encode ((checkpoint_write s a t o src empty zero length).1 i.val i.isLt)

/-- Single computed write, protected transaction history, actual TX2 shared
acquisition/read/drop. The loaded entry bytes are derived, not separately
assumed at save/tx2/resume sites. Runtime account indices remain explicit. -/
theorem entry_write_history {W F : Type} (L : Library W F)
    (trust : S2TrustedSdkBorrow L) (encode : UInt8 → Byte)
    (savedState entryState : Heap F) (w : W)
    (writer reader writeToken writeOwner readToken readOwner : Nat) (src : Payload)
    (empty : savedState.guards = [])
    (zero : savedState.counter (savedState.accounts writer).1 = 0)
    (length : (savedState.payload (savedState.accounts writer).1).descriptor.length = 1768)
    (keys : Nat → List UInt8) (n : Nat)
    (entry : RuntimeEntrypointAdmission entryState keys n) (within : reader < n)
    (related : L.related w entryState)
    (version : S2X.CheckpointVersionBinding
      (payloadBytes encode ((writeBracket savedState writer writeToken writeOwner src).payload
        (savedState.accounts writer).1) 1768)
      (payloadBytes encode (entryState.payload (entryState.accounts reader).1) 1768)) :
    payloadBytes encode (entryState.payload (entryState.accounts reader).1) 1768 =
      payloadBytes encode src 1768 ∧
    (payloadBytes encode src 1768).length = 1768 ∧
    ∃ acquired read done,
      L.run w (.shared reader readToken readOwner) = (acquired,.guard readToken) ∧
      L.run acquired (.deref readToken) =
        (read,.payload (entryState.payload (entryState.accounts reader).1)) ∧
      L.run read (.drop readToken) = (done,.unit) ∧ L.related done entryState := by
  refine ⟨?_,?_,native_snapshot_protocol L trust w entryState keys n reader readToken
    readOwner entry within related⟩
  · exact (S2X.checkpoint_persistence _ _ version).trans
      (written_bytes encode savedState writer writeToken writeOwner src empty zero length)
  · exact List.length_ofFn

#print axioms written_bytes
#print axioms entry_write_history
end AspisR1.S2W_EntryWriteHistory
