import R1Z.PDict_ResumeDictionary
set_option autoImplicit false
noncomputable section
namespace R1Z.PDict_OffpathBorrow
open Aeneas Aeneas.Std Result ProverRwFull
section Source
variable [ExternalTypes]
def derefMut
  {Z : Type} (ZeroizeInst : zeroize.Zeroize Z) (self : zeroize.Zeroizing Z) :
  Result (Z × (Z → zeroize.Zeroizing Z))
  := do
  let back := fun t => t
  ok (self, back)

def asMut
  {T : Type} {Z : Type} (coreconvertAsMutInst : core.convert.AsMut Z T)
  (ZeroizeInst : zeroize.Zeroize Z) (self : zeroize.Zeroizing Z) :
  Result (T × (T → zeroize.Zeroizing Z))
  := do
  let (t, as_mut_back) ← coreconvertAsMutInst.as_mut self
  let back := fun t1 => let t2 := as_mut_back t1
                        t2
  ok (t, back)


end Source
abbrev native := PDict_ResumeDictionary.native
@[reducible] def selected (base : ExternalTypes)
    (ops : @ExternalFuns (native base)) : @ExternalFuns (native base) :=
  letI : ExternalTypes := native base
  { PDict_ResumeDictionary.selected base ops with op125 := asMut, op126 := derefMut }

theorem op125_installed (base : ExternalTypes) (ops : @ExternalFuns (native base)) :
    @ExternalFuns.op125 (native base) (selected base ops) = @asMut := rfl

theorem op126_installed (base : ExternalTypes) (ops : @ExternalFuns (native base)) :
    @ExternalFuns.op126 (native base) (selected base ops) = @derefMut := rfl

#print axioms op125_installed
#print axioms op126_installed
end R1Z.PDict_OffpathBorrow
