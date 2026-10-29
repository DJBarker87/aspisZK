import R1Z.PV_OWND_LegacySource
set_option autoImplicit false
namespace R1Z.PV_OWND_Private01
open PV_OWN_Link PV_OWND_LegacySource
/-- One bounded source iteration, with all kind payloads retained. -/
def values : List Link := [⟨.privatePathCurrent 1,75,867⟩,⟨.privatePathLeft 1,868,92⟩,⟨.privatePathRight 1,868,80⟩]
theorem source : privateLevel 1=values := rfl
theorem base : pathBase 1=some 867 := rfl
#print axioms base
theorem count : values.length=3 := rfl
#print axioms source
#print axioms count
end R1Z.PV_OWND_Private01
