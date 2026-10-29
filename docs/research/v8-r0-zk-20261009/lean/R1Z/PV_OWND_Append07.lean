import R1Z.PV_OWND_LegacySource
set_option autoImplicit false
namespace R1Z.PV_OWND_Append07
open PV_OWN_Link PV_OWND_LegacySource
/-- One bounded source iteration, with all kind payloads retained. -/
def values : List Link := [⟨.appendCurrentLeft 7,651,668⟩,⟨.appendCurrentRight 7,651,656⟩]
theorem source : appendLevel 7=values := rfl
theorem count : values.length=2 := rfl
#print axioms source
#print axioms count
end R1Z.PV_OWND_Append07
