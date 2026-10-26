import CPH_FixtureData
set_option autoImplicit false
noncomputable section
namespace AspisR1.CPH_FixtureKeys
open Aeneas Aeneas.Std Result S2Trust S2W_D189Entry S2W_D189Wrappers
open CPH_FixtureData

theorem byte_value (n : Nat) (bound : n < 256) : (byte n).val = n := by
  simp [byte,Nat.mod_eq_of_lt bound]

theorem key_injective (i j : Nat) (hi : i < 256) (hj : j < 256)
    (same : key i = key j) : i = j := by
  have head := congrArg (fun k : S2W_ExtractionBoundary.Program => k.val[0]?) same
  change some (byte i) = some (byte j) at head
  have values := congrArg (fun v : U8 => v.val) (Option.some.inj head)
  simpa only [byte_value i hi,byte_value j hj] using values

#print axioms byte_value
#print axioms key_injective
end AspisR1.CPH_FixtureKeys
end
