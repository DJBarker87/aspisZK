import R1Z.PV_OWND_LegacySource
set_option autoImplicit false
namespace R1Z.PV_OWND_Private16
open PV_OWN_Link PV_OWND_LegacySource
/-- One bounded source iteration, with all kind payloads retained. -/
def values : List Link := [⟨.privatePathCurrent 16,315,929⟩,⟨.privatePathLeft 16,930,332⟩,⟨.privatePathRight 16,930,320⟩]
theorem source : privateLevel 16=values := rfl
theorem base : pathBase 16=some 929 := rfl
#print axioms base
theorem count : values.length=3 := rfl
#print axioms source
#print axioms count
end R1Z.PV_OWND_Private16
