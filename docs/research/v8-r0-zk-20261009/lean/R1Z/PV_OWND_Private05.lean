import R1Z.PV_OWND_LegacySource
set_option autoImplicit false
namespace R1Z.PV_OWND_Private05
open PV_OWN_Link PV_OWND_LegacySource
/-- One bounded source iteration, with all kind payloads retained. -/
def values : List Link := [⟨.privatePathCurrent 5,139,883⟩,⟨.privatePathLeft 5,884,156⟩,⟨.privatePathRight 5,884,144⟩]
theorem source : privateLevel 5=values := rfl
theorem base : pathBase 5=some 883 := rfl
#print axioms base
theorem count : values.length=3 := rfl
#print axioms source
#print axioms count
end R1Z.PV_OWND_Private05
