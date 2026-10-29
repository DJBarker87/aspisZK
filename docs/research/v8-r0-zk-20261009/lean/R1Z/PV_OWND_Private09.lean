import R1Z.PV_OWND_LegacySource
set_option autoImplicit false
namespace R1Z.PV_OWND_Private09
open PV_OWN_Link PV_OWND_LegacySource
/-- One bounded source iteration, with all kind payloads retained. -/
def values : List Link := [⟨.privatePathCurrent 9,203,899⟩,⟨.privatePathLeft 9,900,220⟩,⟨.privatePathRight 9,900,208⟩]
theorem source : privateLevel 9=values := rfl
theorem base : pathBase 9=some 899 := rfl
#print axioms base
theorem count : values.length=3 := rfl
#print axioms source
#print axioms count
end R1Z.PV_OWND_Private09
