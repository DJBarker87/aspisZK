import R1Z.PV_OWND_LegacySource
set_option autoImplicit false
namespace R1Z.PV_OWND_FixedPhases
open PV_OWN_Link PV_OWND_LegacySource

def spongeValues : List Link := [⟨.spongeCarry 1 2,27,32⟩,⟨.spongeCarry 2 3,43,48⟩,
 ⟨.spongeCarry 25 26,411,416⟩,⟨.spongeCarry 27 28,443,448⟩,
 ⟨.spongeCarry 28 29,459,464⟩,⟨.spongeCarry 30 31,491,496⟩,⟨.spongeCarry 31 32,507,512⟩]
theorem sponge_source : sponge=spongeValues := rfl
theorem sponge_count : sponge.length=7 := rfl
theorem head_count : head.length=4 := rfl
def valueValues : List Link := [⟨.valueSource 0,44,960⟩,⟨.valueSource 1,460,962⟩,⟨.valueSource 2,508,964⟩]
theorem value_source : valueSources=valueValues := rfl
theorem value_count : valueSources.length=3 := rfl
theorem conservation_count : conservation.length=4 := rfl
theorem occupancy_count : occupancy.length=6 := rfl
#print axioms sponge_source
#print axioms sponge_count
#print axioms head_count
#print axioms value_source
#print axioms value_count
#print axioms conservation_count
#print axioms occupancy_count
end R1Z.PV_OWND_FixedPhases
