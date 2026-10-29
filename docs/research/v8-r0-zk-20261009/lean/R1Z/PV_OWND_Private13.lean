import R1Z.PV_OWND_LegacySource
set_option autoImplicit false
namespace R1Z.PV_OWND_Private13
open PV_OWN_Link PV_OWND_LegacySource
/-- One bounded source iteration, with all kind payloads retained. -/
def values : List Link := [⟨.privatePathCurrent 13,267,915⟩,⟨.privatePathLeft 13,916,284⟩,⟨.privatePathRight 13,916,272⟩]
theorem source : privateLevel 13=values := rfl
theorem base : pathBase 13=some 915 := rfl
#print axioms base
theorem count : values.length=3 := rfl
#print axioms source
#print axioms count
end R1Z.PV_OWND_Private13
