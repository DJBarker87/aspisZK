import R1Z.PV_OWND_LegacySource
set_option autoImplicit false
namespace R1Z.PV_OWND_Append04
open PV_OWN_Link PV_OWND_LegacySource
/-- One bounded source iteration, with all kind payloads retained. -/
def values : List Link := [⟨.appendCurrentLeft 4,603,620⟩,⟨.appendCurrentRight 4,603,608⟩]
theorem source : appendLevel 4=values := rfl
theorem count : values.length=2 := rfl
#print axioms source
#print axioms count
end R1Z.PV_OWND_Append04
