import R1Z.PV_OWND_LegacySource
set_option autoImplicit false
namespace R1Z.PV_OWND_Private19
open PV_OWN_Link PV_OWND_LegacySource
/-- One bounded source iteration, with all kind payloads retained. -/
def values : List Link := [⟨.privatePathCurrent 19,363,935⟩,⟨.privatePathLeft 19,936,380⟩,⟨.privatePathRight 19,936,368⟩]
theorem source : privateLevel 19=values := rfl
theorem base : pathBase 19=some 935 := rfl
#print axioms base
theorem count : values.length=3 := rfl
#print axioms source
#print axioms count
end R1Z.PV_OWND_Private19
