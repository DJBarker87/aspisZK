import R1Z.PV_OWND_LegacySource
set_option autoImplicit false
namespace R1Z.PV_OWND_Private06
open PV_OWN_Link PV_OWND_LegacySource
/-- One bounded source iteration, with all kind payloads retained. -/
def values : List Link := [⟨.privatePathCurrent 6,155,885⟩,⟨.privatePathLeft 6,886,172⟩,⟨.privatePathRight 6,886,160⟩]
theorem source : privateLevel 6=values := rfl
theorem base : pathBase 6=some 885 := rfl
#print axioms base
theorem count : values.length=3 := rfl
#print axioms source
#print axioms count
end R1Z.PV_OWND_Private06
