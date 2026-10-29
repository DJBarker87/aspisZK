import R1Z.PV_OWND_LegacySource
set_option autoImplicit false
namespace R1Z.PV_OWND_Private15
open PV_OWN_Link PV_OWND_LegacySource
/-- One bounded source iteration, with all kind payloads retained. -/
def values : List Link := [⟨.privatePathCurrent 15,299,919⟩,⟨.privatePathLeft 15,920,316⟩,⟨.privatePathRight 15,920,304⟩]
theorem source : privateLevel 15=values := rfl
theorem base : pathBase 15=some 919 := rfl
#print axioms base
theorem count : values.length=3 := rfl
#print axioms source
#print axioms count
end R1Z.PV_OWND_Private15
