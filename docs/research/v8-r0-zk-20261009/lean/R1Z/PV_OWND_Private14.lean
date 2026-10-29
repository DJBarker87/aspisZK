import R1Z.PV_OWND_LegacySource
set_option autoImplicit false
namespace R1Z.PV_OWND_Private14
open PV_OWN_Link PV_OWND_LegacySource
/-- One bounded source iteration, with all kind payloads retained. -/
def values : List Link := [⟨.privatePathCurrent 14,283,917⟩,⟨.privatePathLeft 14,918,300⟩,⟨.privatePathRight 14,918,288⟩]
theorem source : privateLevel 14=values := rfl
theorem base : pathBase 14=some 917 := rfl
#print axioms base
theorem count : values.length=3 := rfl
#print axioms source
#print axioms count
end R1Z.PV_OWND_Private14
