import SelectorValueLaneGeneratedSlice

/-! Exact generated domain constants used by initial schedule lanes.
Only the module framing and isolating namespace are changed. -/
open Aeneas Aeneas.Std Result
namespace AspisR1ScheduleDomainCandidate
open AspisR1SelectedMaskProbe

/-- [aspis_r1_mask_extraction_probe::spend::DOMAIN_OWNER_KEY]
    Source: 'src/statement/spend.rs', lines 14:0-14:58 -/
@[global_simps, irreducible]
def spend.DOMAIN_OWNER_KEY : field.M31 := 1095958529#u32

/-- [aspis_r1_mask_extraction_probe::spend::DOMAIN_NOTE]
    Source: 'src/statement/spend.rs', lines 16:0-16:53 -/
@[global_simps, irreducible]
def spend.DOMAIN_NOTE : field.M31 := 1095958531#u32

/-- [aspis_r1_mask_extraction_probe::spend::DOMAIN_NULLIFIER]
    Source: 'src/statement/spend.rs', lines 15:0-15:58 -/
@[global_simps, irreducible]
def spend.DOMAIN_NULLIFIER : field.M31 := 1095958530#u32

end AspisR1ScheduleDomainCandidate
