import R1Z.PV_OWND_LegacySource
set_option autoImplicit false
namespace R1Z.PV_OWND_Private07
open PV_OWN_Link PV_OWND_LegacySource
/-- One bounded source iteration, with all kind payloads retained. -/
def values : List Link := [⟨.privatePathCurrent 7,171,887⟩,⟨.privatePathLeft 7,888,188⟩,⟨.privatePathRight 7,888,176⟩]
theorem source : privateLevel 7=values := rfl
theorem base : pathBase 7=some 887 := rfl
#print axioms base
theorem count : values.length=3 := rfl
#print axioms source
#print axioms count
end R1Z.PV_OWND_Private07
