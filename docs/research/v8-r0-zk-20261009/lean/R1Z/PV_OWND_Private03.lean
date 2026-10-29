import R1Z.PV_OWND_LegacySource
set_option autoImplicit false
namespace R1Z.PV_OWND_Private03
open PV_OWN_Link PV_OWND_LegacySource
/-- One bounded source iteration, with all kind payloads retained. -/
def values : List Link := [⟨.privatePathCurrent 3,107,871⟩,⟨.privatePathLeft 3,872,124⟩,⟨.privatePathRight 3,872,112⟩]
theorem source : privateLevel 3=values := rfl
theorem base : pathBase 3=some 871 := rfl
#print axioms base
theorem count : values.length=3 := rfl
#print axioms source
#print axioms count
end R1Z.PV_OWND_Private03
