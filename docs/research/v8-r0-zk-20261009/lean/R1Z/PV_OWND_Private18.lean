import R1Z.PV_OWND_LegacySource
set_option autoImplicit false
namespace R1Z.PV_OWND_Private18
open PV_OWN_Link PV_OWND_LegacySource
/-- One bounded source iteration, with all kind payloads retained. -/
def values : List Link := [⟨.privatePathCurrent 18,347,933⟩,⟨.privatePathLeft 18,934,364⟩,⟨.privatePathRight 18,934,352⟩]
theorem source : privateLevel 18=values := rfl
theorem base : pathBase 18=some 933 := rfl
#print axioms base
theorem count : values.length=3 := rfl
#print axioms source
#print axioms count
end R1Z.PV_OWND_Private18
