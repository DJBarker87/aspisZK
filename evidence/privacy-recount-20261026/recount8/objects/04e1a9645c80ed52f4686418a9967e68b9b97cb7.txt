import R1Z.PV_RDB2_LayoutPad
import R1Z.PV_RDB2_ConstructorEffects

/-! Reallocation argument/effect transport, and a reference for the required
preserved-prefix property. The latter is not credited as a native allocator
law without the concrete hook/resource-family association. -/
namespace R1Z.PV_RDB2_Realloc
set_option autoImplicit false
open Aeneas Aeneas.Std Result PV_RDB2_Alignment PV_RDB2_LayoutPad

def oldCall {Pointer World : Type}
    (reallocate : Pointer → Nat → Nat → Nat → World → Result (Pointer × World))
    (pointer : Pointer) (old : TypedLayout) (newSize : Nat) (world : World) :=
  reallocate pointer old.size (oldAsUsize old.alignment) newSize world

def deployedCall {Pointer World : Type}
    (reallocate : Pointer → Nat → Nat → Nat → World → Result (Pointer × World))
    (pointer : Pointer) (old : PV_RDB2_LayoutGuards.Layout) (newSize : Nat) (world : World) :=
  reallocate pointer old.size old.align newSize world

theorem complete {Pointer World : Type}
    (reallocate : Pointer → Nat → Nat → Nat → World → Result (Pointer × World))
    (pointer : Pointer) (old : TypedLayout) (newSize : Nat) (world : World) :
    oldCall reallocate pointer old newSize world =
      deployedCall reallocate pointer (encode old) newSize world := rfl

def resized {T : Type} (old : Nat → Option T) (oldSize newSize : Nat) (i : Nat) : Option T :=
  if i < min oldSize newSize then old i else none

theorem prefix_preserved {T : Type} (old : Nat → Option T) (oldSize newSize i : Nat)
    (h : i < oldSize) (hnew : i < newSize) :
    resized old oldSize newSize i = old i := if_pos (by omega)

theorem new_suffix_uninitialized {T : Type} (old : Nat → Option T) (oldSize newSize i : Nat)
    (h : oldSize ≤ i) : resized old oldSize newSize i = none := if_neg (by omega)

theorem shrink_discards_only_suffix {T : Type} (old : Nat → Option T) (oldSize newSize i : Nat)
    (shrinking : newSize ≤ oldSize) (retained : i < newSize) :
    resized old oldSize newSize i = old i := prefix_preserved old oldSize newSize i (by omega) retained

#print axioms complete
#print axioms prefix_preserved
#print axioms new_suffix_uninitialized
#print axioms shrink_discards_only_suffix
end R1Z.PV_RDB2_Realloc
