import R1Z.PV_RDB2_Alignment

/-! Transport of pad_to_align and the typed/usize unchecked constructors.
The rounding helper is the same source body after the checked source-name
renaming. Its numerical correctness is not assumed as a new trust item. -/
namespace R1Z.PV_RDB2_LayoutPad
set_option autoImplicit false
open Aeneas Aeneas.Std Result PV_RDB2_Alignment

structure TypedLayout where
  size : Nat
  alignment : Alignment

def encode (self : TypedLayout) : PV_RDB2_LayoutGuards.Layout :=
  ⟨self.size,word self.alignment⟩

def oldPad (round : Nat → Nat → Nat) (self : TypedLayout) : TypedLayout :=
  ⟨round self.size (oldAsUsize self.alignment),self.alignment⟩

def deployedPad (round : Nat → Nat → Nat) (self : PV_RDB2_LayoutGuards.Layout) :
    PV_RDB2_LayoutGuards.Layout := ⟨round self.size self.align,self.align⟩

theorem complete (round : Nat → Nat → Nat) (self : TypedLayout) :
    encode (oldPad round self) = deployedPad round (encode self) := rfl

theorem complete_effect {World : Type} (round : Nat → Nat → Nat)
    (self : TypedLayout) (world : World) :
    (ok (encode (oldPad round self),world) : Result (PV_RDB2_LayoutGuards.Layout × World)) =
      ok (deployedPad round (encode self),world) := rfl

theorem unchanged_alignment (round : Nat → Nat → Nat) (self : TypedLayout) :
    (deployedPad round (encode self)).align = word self.alignment := rfl

#print axioms complete
#print axioms complete_effect
#print axioms unchanged_alignment
end R1Z.PV_RDB2_LayoutPad
