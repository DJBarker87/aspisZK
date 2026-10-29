import R1Z.PV_OWND_LegacySource
set_option autoImplicit false
namespace R1Z.PV_OWND_Private02
open PV_OWN_Link PV_OWND_LegacySource
/-- One bounded source iteration, with all kind payloads retained. -/
def values : List Link := [⟨.privatePathCurrent 2,91,869⟩,⟨.privatePathLeft 2,870,108⟩,⟨.privatePathRight 2,870,96⟩]
theorem source : privateLevel 2=values := rfl
theorem base : pathBase 2=some 869 := rfl
#print axioms base
theorem count : values.length=3 := rfl
#print axioms source
#print axioms count
end R1Z.PV_OWND_Private02
