import R1Z.PDict_CodecDictionary
import R1Z.ProverRwEffectSource
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_ZeroizingPrefix
open Aeneas Aeneas.Std Result ProverRwFull

/-- Existing retained value carrier. No type is changed; physical cleanup
and volatile-store effects remain separate obligations. -/
abbrev native (base : ExternalTypes) := PDict_CodecDictionary.native base

def newValue {Z : Type} (_ : zeroize.Zeroize Z) (z : Z) : Result Z := .ok z

def asMut {T Z : Type} (inst : core.convert.AsMut Z T)
    (_ : zeroize.Zeroize Z) (value : Z) : Result (T × (T → Z)) :=
  inst.as_mut value

@[reducible] def selected (base : ExternalTypes) (ops : @ExternalFuns (native base)) :
    @ExternalFuns (native base) := by
  letI : ExternalTypes := native base
  exact {PDict_CodecDictionary.selected base ops with op128 := @newValue,op125 := @asMut}

theorem type_installed (base : ExternalTypes) (Z : Type) :
    zeroize.Zeroizing Z = Z := rfl

#print axioms type_installed
end R1Z.PV_RunJoin_ZeroizingPrefix
