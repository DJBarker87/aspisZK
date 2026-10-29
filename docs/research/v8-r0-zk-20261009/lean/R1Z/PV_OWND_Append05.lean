import R1Z.PV_OWND_LegacySource
set_option autoImplicit false
namespace R1Z.PV_OWND_Append05
open PV_OWN_Link PV_OWND_LegacySource
/-- One bounded source iteration, with all kind payloads retained. -/
def values : List Link := [⟨.appendCurrentLeft 5,619,636⟩,⟨.appendCurrentRight 5,619,624⟩]
theorem source : appendLevel 5=values := rfl
theorem count : values.length=2 := rfl
#print axioms source
#print axioms count
end R1Z.PV_OWND_Append05
