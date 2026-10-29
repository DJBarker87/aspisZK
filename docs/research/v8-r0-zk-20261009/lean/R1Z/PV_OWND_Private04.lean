import R1Z.PV_OWND_LegacySource
set_option autoImplicit false
namespace R1Z.PV_OWND_Private04
open PV_OWN_Link PV_OWND_LegacySource
/-- One bounded source iteration, with all kind payloads retained. -/
def values : List Link := [⟨.privatePathCurrent 4,123,881⟩,⟨.privatePathLeft 4,882,140⟩,⟨.privatePathRight 4,882,128⟩]
theorem source : privateLevel 4=values := rfl
theorem base : pathBase 4=some 881 := rfl
#print axioms base
theorem count : values.length=3 := rfl
#print axioms source
#print axioms count
end R1Z.PV_OWND_Private04
