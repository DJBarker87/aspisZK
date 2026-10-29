import R1Z.PV_OWND_LegacySource
set_option autoImplicit false
namespace R1Z.PV_OWND_Private10
open PV_OWN_Link PV_OWND_LegacySource
/-- One bounded source iteration, with all kind payloads retained. -/
def values : List Link := [⟨.privatePathCurrent 10,219,901⟩,⟨.privatePathLeft 10,902,236⟩,⟨.privatePathRight 10,902,224⟩]
theorem source : privateLevel 10=values := rfl
theorem base : pathBase 10=some 901 := rfl
#print axioms base
theorem count : values.length=3 := rfl
#print axioms source
#print axioms count
end R1Z.PV_OWND_Private10
