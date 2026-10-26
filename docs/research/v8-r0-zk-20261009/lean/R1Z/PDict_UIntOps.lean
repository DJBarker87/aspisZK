import R1Z.PDict_CarrierInstall
import R1Z.PDict_Installed
set_option autoImplicit false
noncomputable section
namespace R1Z.PDict_UIntOps
open Aeneas Aeneas.Std Result ProverRwFull
abbrev UInt := PDict_UInt.typenum.uint.UInt

def cmp10 {L R S O : Type} (_ : typenum.marker_traits.Unsigned L)
    (_ : typenum.marker_traits.Unsigned R) (_ : typenum.marker_traits.Ord S)
    (next : typenum.private.PrivateCmp L R typenum.Greater O)
    (a : UInt L typenum.bit.B1) (b : UInt R typenum.bit.B0) (_ : S) : Result O :=
  next.private_cmp a.msb b.msb ()

def cmpSame {L R S O : Type} (_ : typenum.marker_traits.Unsigned L)
    (_ : typenum.marker_traits.Unsigned R) (_ : typenum.marker_traits.Ord S)
    (next : typenum.private.PrivateCmp L R S O)
    (a : UInt L Unit) (b : UInt R Unit) (s : S) : Result O :=
  next.private_cmp a.msb b.msb s

def compare {L R IM O : Type} (_ : typenum.marker_traits.Unsigned L)
    (_ : typenum.marker_traits.Unsigned R)
    (next : typenum.private.PrivateCmp L R typenum.Equal O)
    (_ : typenum.private.InternalMarker IM)
    (a : UInt L typenum.bit.B0) (b : UInt R typenum.bit.B0) : Result O :=
  next.private_cmp a.msb b.msb ()

def makeDefault {U B : Type} (u : core.default.Default U)
    (b : core.default.Default B) : Result (UInt U B) := do
  let msb ← u.default
  let lsb ← b.default
  .ok ⟨msb,lsb⟩

def clone {U B : Type} (u : core.clone.Clone U) (b : core.clone.Clone B)
    (x : UInt U B) : Result (UInt U B) := do
  let msb ← u.clone x.msb
  let lsb ← b.clone x.lsb
  .ok ⟨msb,lsb⟩

@[reducible] def selected (base : ExternalTypes)
    (ops : @ExternalFuns (PDict_CarrierInstall.native base)) :
    @ExternalFuns (PDict_CarrierInstall.native base) :=
  letI : ExternalTypes := PDict_CarrierInstall.native base
  { @PDict_Installed.selected (PDict_CarrierInstall.native base) ops with
    op137 := @cmp10, op138 := @cmpSame, op139 := @cmpSame,
    op140 := @compare, op161 := @makeDefault, op162 := @clone }

theorem op137_installed (base : ExternalTypes)
    (ops : @ExternalFuns (PDict_CarrierInstall.native base)) {L R S O : Type}
    (l : typenum.marker_traits.Unsigned L) (r : typenum.marker_traits.Unsigned R)
    (s : typenum.marker_traits.Ord S)
    (next : typenum.private.PrivateCmp L R typenum.Greater O)
    (a : UInt L typenum.bit.B1) (b : UInt R typenum.bit.B0) (state : S) :
    (selected base ops).op137 l r s next a b state = next.private_cmp a.msb b.msb () := rfl

theorem op138_installed (base : ExternalTypes)
    (ops : @ExternalFuns (PDict_CarrierInstall.native base)) {L R S O : Type}
    (l : typenum.marker_traits.Unsigned L) (r : typenum.marker_traits.Unsigned R)
    (s : typenum.marker_traits.Ord S) (next : typenum.private.PrivateCmp L R S O)
    (a : UInt L typenum.bit.B1) (b : UInt R typenum.bit.B1) (state : S) :
    (selected base ops).op138 l r s next a b state = next.private_cmp a.msb b.msb state := rfl

theorem op139_installed (base : ExternalTypes)
    (ops : @ExternalFuns (PDict_CarrierInstall.native base)) {L R S O : Type}
    (l : typenum.marker_traits.Unsigned L) (r : typenum.marker_traits.Unsigned R)
    (s : typenum.marker_traits.Ord S) (next : typenum.private.PrivateCmp L R S O)
    (a : UInt L typenum.bit.B0) (b : UInt R typenum.bit.B0) (state : S) :
    (selected base ops).op139 l r s next a b state = next.private_cmp a.msb b.msb state := rfl

theorem op140_installed (base : ExternalTypes)
    (ops : @ExternalFuns (PDict_CarrierInstall.native base)) {L R O IM : Type}
    (l : typenum.marker_traits.Unsigned L) (r : typenum.marker_traits.Unsigned R)
    (next : typenum.private.PrivateCmp L R typenum.Equal O)
    (marker : typenum.private.InternalMarker IM)
    (a : UInt L typenum.bit.B0) (b : UInt R typenum.bit.B0) :
    (selected base ops).op140 l r next marker a b = next.private_cmp a.msb b.msb () := rfl

theorem op161_installed (base : ExternalTypes)
    (ops : @ExternalFuns (PDict_CarrierInstall.native base)) {U B : Type}
    (u : core.default.Default U) (b : core.default.Default B) :
    (selected base ops).op161 u b = makeDefault u b := rfl

theorem op162_installed (base : ExternalTypes)
    (ops : @ExternalFuns (PDict_CarrierInstall.native base)) {U B : Type}
    (u : core.clone.Clone U) (b : core.clone.Clone B) (x : UInt U B) :
    (selected base ops).op162 u b x = clone u b x := rfl

#print axioms op137_installed
#print axioms op138_installed
#print axioms op139_installed
#print axioms op140_installed
#print axioms op161_installed
#print axioms op162_installed
end R1Z.PDict_UIntOps
