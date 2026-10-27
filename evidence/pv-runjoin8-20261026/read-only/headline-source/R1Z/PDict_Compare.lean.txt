import R1Z.PDict_Numeric
set_option autoImplicit false
noncomputable section
namespace R1Z.PDict_Compare
open Aeneas Aeneas.Std Result ProverRwFull

def terminal {S : Type} (_ : typenum.marker_traits.Ord S)
    (_ _ : typenum.uint.UTerm) (s : S) : Result S := .ok s

def equalTrue {A B : Type} (_ : A) (_ : B) (_ : typenum.Equal) :
    Result typenum.bit.B1 := .ok ()

def lessTrue {A B : Type} (_ : A) (_ : B) (_ : typenum.Less) :
    Result typenum.bit.B1 := .ok ()

variable [ExternalTypes]
def terminalLess {U B S : Type} (_ : typenum.marker_traits.Unsigned U)
    (_ : typenum.marker_traits.Bit B) (_ : typenum.marker_traits.Ord S)
    (_ : typenum.uint.UTerm) (_ : typenum.uint.UInt U B) (_ : S) :
    Result typenum.Less := .ok ()

@[reducible] def selected (ops : ExternalFuns) : ExternalFuns :=
  { PDict_Numeric.selected ops with
    op135 := @terminal, op136 := @terminalLess _,
    op187 := @equalTrue, op195 := @lessTrue }

theorem op135_installed (ops : ExternalFuns) {S : Type}
    (o : typenum.marker_traits.Ord S) (a b : typenum.uint.UTerm) (s : S) :
    (selected ops).op135 o a b s = .ok s := rfl

theorem op136_installed (ops : ExternalFuns) {U B S : Type}
    (u : typenum.marker_traits.Unsigned U) (b : typenum.marker_traits.Bit B)
    (o : typenum.marker_traits.Ord S) (a : typenum.uint.UTerm)
    (n : typenum.uint.UInt U B) (s : S) :
    (selected ops).op136 u b o a n s = .ok () := rfl

theorem op187_installed (ops : ExternalFuns) {A B : Type}
    (a : A) (b : B) (c : typenum.Equal) :
    (selected ops).op187 a b c = .ok () := rfl

theorem op195_installed (ops : ExternalFuns) {A B : Type}
    (a : A) (b : B) (c : typenum.Less) :
    (selected ops).op195 a b c = .ok () := rfl

#print axioms op135_installed
#print axioms op136_installed
#print axioms op187_installed
#print axioms op195_installed
end R1Z.PDict_Compare
