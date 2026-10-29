import R1Z.PV_OWND_LegacySource
set_option autoImplicit false
namespace R1Z.PV_OWND_Private17
open PV_OWN_Link PV_OWND_LegacySource
/-- One bounded source iteration, with all kind payloads retained. -/
def values : List Link := [⟨.privatePathCurrent 17,331,931⟩,⟨.privatePathLeft 17,932,348⟩,⟨.privatePathRight 17,932,336⟩]
theorem source : privateLevel 17=values := rfl
theorem base : pathBase 17=some 931 := rfl
#print axioms base
theorem count : values.length=3 := rfl
#print axioms source
#print axioms count
end R1Z.PV_OWND_Private17
