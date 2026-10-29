import R1Z.PV_OWND_LegacySource
set_option autoImplicit false
namespace R1Z.PV_OWND_Private12
open PV_OWN_Link PV_OWND_LegacySource
/-- One bounded source iteration, with all kind payloads retained. -/
def values : List Link := [⟨.privatePathCurrent 12,251,913⟩,⟨.privatePathLeft 12,914,268⟩,⟨.privatePathRight 12,914,256⟩]
theorem source : privateLevel 12=values := rfl
theorem base : pathBase 12=some 913 := rfl
#print axioms base
theorem count : values.length=3 := rfl
#print axioms source
#print axioms count
end R1Z.PV_OWND_Private12
