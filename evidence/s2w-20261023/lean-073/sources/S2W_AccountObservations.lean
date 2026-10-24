import S2W_CommittedCheckpoint

/-! Full account observations computed from heap states. Inaccessible indices
have no native data cell and retain the ambient record. The lens includes all
Account fields, including lamports/rentEpoch absent from OwnedAccount.
This is an interpreted wrapper theorem, not a native-wrapper extraction law. -/
set_option autoImplicit false
namespace AspisR1.S2W_AccountObservations
open S2Trust S2W_TrustedStd S2W_WrapperLaws S2W_EntryWriteHistory
open AspisV8R19.DuplexFrames

def observe {F : Type} (encode : UInt8 → AspisV8R19.DuplexFrames.Byte)
    (metadata : F → Nat → S2LeadInterface.Account) (n : Nat) (s : Heap F)
    (a : Nat) : S2LeadInterface.Account :=
  if a < n then
    {metadata s.ambient a with data := payloadBytes encode (s.payload (s.accounts a).1)
      (s.payload (s.accounts a).1).descriptor.length}
  else metadata s.ambient a

/-- Snapshot's actual shared acquire/drop bracket changes no account record.
The copy/allocation source port remains separate, as in the imported SDK law. -/
theorem snapshot_frame {F : Type} (encode : UInt8 → AspisV8R19.DuplexFrames.Byte)
    (metadata : F → Nat → S2LeadInterface.Account) (n : Nat) (s : Heap F)
    (keys : Nat → List UInt8) (a token owner : Nat)
    (runtime : AdapterRw.RuntimeEntrypointAdmission s keys n) (within : a < n) :
    observe encode metadata n (AdapterRw.Snapshots.sharedBracket s a token owner) =
      observe encode metadata n s := by
  rw [AdapterRw.Snapshots.entry_bracket_restores runtime within token owner]

/-- Lift the checked wrapper's single-cell frame to full account records.
Alias exclusion is explicit, not inferred merely from unequal slot numbers. -/
theorem write_frame {F : Type} (encode : UInt8 → AspisV8R19.DuplexFrames.Byte)
    (metadata : F → Nat → S2LeadInterface.Account) (n : Nat) (s : Heap F)
    (writer token owner : Nat) (src : Payload)
    (empty : s.guards = []) (zero : s.counter (s.accounts writer).1 = 0)
    (a : Nat) (disjoint : a < n → (s.accounts a).1 ≠ (s.accounts writer).1) :
    observe encode metadata n (writeBracket s writer token owner src) a =
      observe encode metadata n s a := by
  rw [write_bracket s writer token owner src empty zero]
  by_cases within : a < n
  · simp [observe,within,copyHeap,put,disjoint within]
  · simp [observe,within,copyHeap]

/-- The written account's entire metadata record is unchanged. No account
post-state or metadata equation is a premise. -/
theorem write_metadata {F : Type} (encode : UInt8 → AspisV8R19.DuplexFrames.Byte)
    (metadata : F → Nat → S2LeadInterface.Account) (n : Nat) (s : Heap F)
    (writer token owner : Nat) (src : Payload)
    (empty : s.guards = []) (zero : s.counter (s.accounts writer).1 = 0) :
    {observe encode metadata n (writeBracket s writer token owner src) writer with
      data := (observe encode metadata n s writer).data} = observe encode metadata n s writer := by
  rw [write_bracket s writer token owner src empty zero]
  by_cases within : writer < n
  · simp [observe,within,copyHeap]
  · simp [observe,within,copyHeap]

/-- Runtime key/cell admission discharges the local alias-exclusion condition
for an accessible account with a different key from the checkpoint account. -/
theorem admitted_write_frame {F : Type} (encode : UInt8 → AspisV8R19.DuplexFrames.Byte)
    (metadata : F → Nat → S2LeadInterface.Account) (n : Nat) (s : Heap F)
    (keys : Nat → List UInt8) (writer token owner : Nat) (src : Payload)
    (runtime : AdapterRw.RuntimeEntrypointAdmission s keys n) (writerWithin : writer < n)
    (a : Nat) (different : a < n → keys a ≠ keys writer) :
    observe encode metadata n (writeBracket s writer token owner src) a =
      observe encode metadata n s a := by
  apply write_frame encode metadata n s writer token owner src runtime.freshGuards
    (runtime.counterZero writer writerWithin) a
  intro within
  exact AdapterRw.distinct_keys_distinct_cells runtime within writerWithin (different within)

#print axioms snapshot_frame
#print axioms write_frame
#print axioms write_metadata
#print axioms admitted_write_frame
end AspisR1.S2W_AccountObservations
