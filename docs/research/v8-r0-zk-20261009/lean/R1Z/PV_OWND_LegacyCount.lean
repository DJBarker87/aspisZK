import R1Z.PV_OWND_PrivatePhase
import R1Z.PV_OWND_AppendPhase
import R1Z.PV_OWND_FixedPhases
set_option autoImplicit false
namespace R1Z.PV_OWND_LegacyCount
open PV_OWND_LegacySource PV_OWND_FixedPhases

theorem private_count : privateLinks.length=63 := by
 rw [PV_OWND_PrivatePhase.source,PV_OWND_PrivatePhase.count]
theorem append_count : appendLinks.length=40 := by
 rw [PV_OWND_AppendPhase.source,PV_OWND_AppendPhase.count]
/-- The literal capacity is derived from the actual kind-preserving phases. -/
theorem count : links.length=127 := by
 unfold links phases
 simp only [List.flatten_cons,List.flatten_nil,List.length_append,List.length_nil,
  sponge_count,head_count,private_count,value_count,conservation_count,occupancy_count,append_count]
#print axioms private_count
#print axioms append_count
#print axioms count
end R1Z.PV_OWND_LegacyCount
