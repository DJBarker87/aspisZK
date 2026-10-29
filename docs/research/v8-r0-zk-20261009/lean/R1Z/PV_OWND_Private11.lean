import R1Z.PV_OWND_LegacySource
set_option autoImplicit false
namespace R1Z.PV_OWND_Private11
open PV_OWN_Link PV_OWND_LegacySource
/-- One bounded source iteration, with all kind payloads retained. -/
def values : List Link := [⟨.privatePathCurrent 11,235,903⟩,⟨.privatePathLeft 11,904,252⟩,⟨.privatePathRight 11,904,240⟩]
theorem source : privateLevel 11=values := rfl
theorem base : pathBase 11=some 903 := rfl
#print axioms base
theorem count : values.length=3 := rfl
#print axioms source
#print axioms count
end R1Z.PV_OWND_Private11
