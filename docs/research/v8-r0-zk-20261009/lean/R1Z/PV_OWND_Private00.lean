import R1Z.PV_OWND_LegacySource
set_option autoImplicit false
namespace R1Z.PV_OWND_Private00
open PV_OWN_Link PV_OWND_LegacySource
/-- One bounded source iteration, with all kind payloads retained. -/
def values : List Link := [⟨.privatePathCurrent 0,59,865⟩,⟨.privatePathLeft 0,866,76⟩,⟨.privatePathRight 0,866,64⟩]
theorem source : privateLevel 0=values := rfl
theorem base : pathBase 0=some 865 := rfl
#print axioms base
theorem count : values.length=3 := rfl
#print axioms source
#print axioms count
end R1Z.PV_OWND_Private00
