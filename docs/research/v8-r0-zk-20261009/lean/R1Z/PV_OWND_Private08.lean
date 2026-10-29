import R1Z.PV_OWND_LegacySource
set_option autoImplicit false
namespace R1Z.PV_OWND_Private08
open PV_OWN_Link PV_OWND_LegacySource
/-- One bounded source iteration, with all kind payloads retained. -/
def values : List Link := [⟨.privatePathCurrent 8,187,897⟩,⟨.privatePathLeft 8,898,204⟩,⟨.privatePathRight 8,898,192⟩]
theorem source : privateLevel 8=values := rfl
theorem base : pathBase 8=some 897 := rfl
#print axioms base
theorem count : values.length=3 := rfl
#print axioms source
#print axioms count
end R1Z.PV_OWND_Private08
