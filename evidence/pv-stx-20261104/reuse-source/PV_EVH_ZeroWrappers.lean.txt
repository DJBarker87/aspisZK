import PV_EVH_DeployedZeroSelected
set_option autoImplicit false
noncomputable section
namespace PV_EVH_ZeroWrappers
open Aeneas Aeneas.Std ProverRwFull
variable [ExternalTypes]

/-- Transparent Zeroizing representation; the mutable dictionary's backward
function is returned unchanged, including all writes supplied by its caller.
No allocator, destructor or physical-memory silence follows from this value law. -/
def asMut {T Z : Type} (d : core.convert.AsMut Z T)
    (_ : zeroize.Zeroize Z) (z : zeroize.Zeroizing Z) :
    Result (T × (T → zeroize.Zeroizing Z)) := d.as_mut z

def derefMut {Z : Type} (_ : zeroize.Zeroize Z) (z : zeroize.Zeroizing Z) :
    Result (Z × (Z → zeroize.Zeroizing Z)) := .ok (z,id)

def deref {Z : Type} (_ : zeroize.Zeroize Z) (z : zeroize.Zeroizing Z) :
    Result Z := .ok z

def new {Z : Type} (_ : zeroize.Zeroize Z) (z : Z) :
    Result (zeroize.Zeroizing Z) := .ok z

def zeroize {Z : Type} (d : zeroize.Zeroize Z) (z : zeroize.Zeroizing Z) :
    Result (zeroize.Zeroizing Z) := d.zeroize z

def asRef {T Z : Type} (d : core.convert.AsRef Z T)
    (_ : zeroize.Zeroize Z) (z : zeroize.Zeroizing Z) : Result T := d.as_ref z

@[reducible] def selected (ops : ExternalFuns) : ExternalFuns :=
  {PV_EVH_DeployedZeroSelected.selected ops with
    op125 := asMut,op126 := derefMut,op127 := deref,op128 := new,
    op130 := zeroize,op131 := asRef}

theorem asMut_restoration {T Z : Type} (d : core.convert.AsMut Z T)
    (dz : zeroize.Zeroize Z) (z : zeroize.Zeroizing Z)
    (a : T) (back : T → Z) (h : d.as_mut z = .ok (a,back)) :
    asMut d dz z = .ok (a,back) := h

theorem derefMut_restoration {Z : Type} (dz : zeroize.Zeroize Z)
    (z updated : Z) :
    (do let (_,back) ← derefMut dz z
        pure (back updated)) = .ok updated := rfl

theorem selected_array (ops : ExternalFuns) {N : Usize} (a : Array U8 N) :
    (selected ops).op122 PV_EVH_DeployedZeroSelected.byteZero a =
      .ok (Array.repeat N 0#u8) := PV_EVH_DeployedZeroSelected.array_value a

theorem constructor (ops : ExternalFuns) {Z : Type} (dz : zeroize.Zeroize Z) (z : Z) :
    (selected ops).op128 dz z = .ok z := rfl

#print axioms asMut_restoration
#print axioms derefMut_restoration
#print axioms selected_array
#print axioms constructor
end PV_EVH_ZeroWrappers
