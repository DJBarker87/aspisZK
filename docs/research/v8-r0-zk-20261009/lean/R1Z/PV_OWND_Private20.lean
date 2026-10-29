import R1Z.PV_OWND_LegacySource
set_option autoImplicit false
namespace R1Z.PV_OWND_Private20
open PV_OWN_Link PV_OWND_LegacySource
/-- One bounded source iteration, with all kind payloads retained. -/
def values : List Link := [⟨.privatePathCurrent 20,379,945⟩,⟨.privatePathLeft 20,946,396⟩,⟨.privatePathRight 20,946,384⟩]
theorem source : privateLevel 20=values := rfl
theorem base : pathBase 20=some 945 := rfl
#print axioms base
theorem count : values.length=3 := rfl
#print axioms source
#print axioms count
end R1Z.PV_OWND_Private20
