import CPH_FixtureData
set_option autoImplicit false
noncomputable section
namespace AspisR1.CPH_FixtureKeys
open Aeneas Aeneas.Std Result S2Trust S2W_D189Entry S2W_D189Wrappers
open CPH_FixtureData

theorem byte_value (n : Nat) (bound : n < 256) : (byte n).val = n := by
  simp [byte,Nat.mod_eq_of_lt bound]

theorem key_injective (i j : Nat) (hi : i < 8) (hj : j < 8)
    (same : key i = key j) : i = j := CPH_RecordedKeys.injective i j hi hj same

#print axioms byte_value
#print axioms key_injective
end AspisR1.CPH_FixtureKeys
end
