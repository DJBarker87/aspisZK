import R1Z.PV_OWND_LegacySource
set_option autoImplicit false
namespace R1Z.PV_OWND_Append02
open PV_OWN_Link PV_OWND_LegacySource
/-- One bounded source iteration, with all kind payloads retained. -/
def values : List Link := [⟨.appendCurrentLeft 2,571,588⟩,⟨.appendCurrentRight 2,571,576⟩]
theorem source : appendLevel 2=values := rfl
theorem count : values.length=2 := rfl
#print axioms source
#print axioms count
end R1Z.PV_OWND_Append02
