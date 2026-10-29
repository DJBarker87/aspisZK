import R1Z.PV_OWN_Link
set_option autoImplicit false
namespace R1Z.PV_OWNB_KindCodec
open PV_OWN_Link
/-- Proposed deployed kind layout. Compiler association is a separate obligation. -/
def tag : Kind → UInt8
 | .spongeCarry _ _ => 0
 | .ownerOutput => 1 | .nullifierKey => 2 | .inputSaltHead => 3 | .inputSaltTail => 4
 | .privatePathCurrent _ => 5 | .privatePathLeft _ => 6 | .privatePathRight _ => 7
 | .valueSource _ => 8
 | .conservationInput => 9 | .conservationRecipient => 10
 | .conservationChange => 11 | .conservationPartial => 12
 | .inputSecondCommitment => 13 | .inputSelectedSide => 14
 | .outputSecondCommitment => 15 | .outputPairFirst => 16
 | .outputPairFirstWithdrawal => 17 | .outputPairSecond => 18
 | .appendCurrentLeft _ => 19 | .appendCurrentRight _ => 20

def first : Kind → Option UInt8
 | .spongeCarry a _ => some a
 | .privatePathCurrent a | .privatePathLeft a | .privatePathRight a | .valueSource a
 | .appendCurrentLeft a | .appendCurrentRight a => some a
 | _ => none

def second : Kind → Option UInt8
 | .spongeCarry _ b => some b
 | _ => none

def encode (k : Kind) (i : Nat) : Option UInt8 :=
 if i=0 then some (tag k) else if i=1 then first k else if i=2 then second k else none

def decode (b : Nat → Option UInt8) : Option Kind := do
 let t ← b 0
 match t.toNat with
 | 0 => return .spongeCarry (← b 1) (← b 2)
 | 1 => return .ownerOutput | 2 => return .nullifierKey
 | 3 => return .inputSaltHead | 4 => return .inputSaltTail
 | 5 => return .privatePathCurrent (← b 1)
 | 6 => return .privatePathLeft (← b 1)
 | 7 => return .privatePathRight (← b 1)
 | 8 => return .valueSource (← b 1)
 | 9 => return .conservationInput | 10 => return .conservationRecipient
 | 11 => return .conservationChange | 12 => return .conservationPartial
 | 13 => return .inputSecondCommitment | 14 => return .inputSelectedSide
 | 15 => return .outputSecondCommitment | 16 => return .outputPairFirst
 | 17 => return .outputPairFirstWithdrawal | 18 => return .outputPairSecond
 | 19 => return .appendCurrentLeft (← b 1)
 | 20 => return .appendCurrentRight (← b 1)
 | _ => none

theorem roundtrip (k : Kind) : decode (encode k)=some k := by
 cases k <;> simp [decode,encode,tag,first,second]

attribute [irreducible] tag first second encode decode
#print axioms roundtrip
end R1Z.PV_OWNB_KindCodec
