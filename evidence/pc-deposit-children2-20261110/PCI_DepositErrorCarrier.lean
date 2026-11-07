import PCI_DepositActual.Types
set_option autoImplicit false
open Aeneas Aeneas.Std
namespace PCI_DepositErrorCarrier
abbrev Error := PCG_ConversionRef.DepositInstructionFormatErrorV1

def tag : Error → Nat
 | .WrongLength => 1 | .WrongMagic => 2 | .WrongVersion => 3 | .NonZeroReserved => 4
 | .InvalidAmount => 5 | .InvalidPayloadLength => 6 | .NonCanonicalDigest => 7

def decode : Nat → Option Error
 | 1 => some .WrongLength | 2 => some .WrongMagic | 3 => some .WrongVersion
 | 4 => some .NonZeroReserved | 5 => some .InvalidAmount | 6 => some .InvalidPayloadLength
 | 7 => some .NonCanonicalDigest | _ => none

theorem roundtrip (e : Error) : decode (tag e)=some e := by cases e <;> rfl

theorem injective (a b : Error) (same : tag a=tag b) : a=b := by
 have h := congrArg decode same
 rw [roundtrip,roundtrip] at h
 exact Option.some.inj h

#print axioms roundtrip
#print axioms injective
end PCI_DepositErrorCarrier
