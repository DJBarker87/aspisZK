-- Local type-only carrier adapter for the generated V10 Types module.
-- The template declares EbyKDot as an axiom; this adapter identifies that
-- external carrier with the already-proved concrete EbyK state type.
import Aeneas
import EbyKPushExplicitTypesV1

namespace fast_pairing

abbrev EbyKDot := AspisR1EbyKPushCutV3.fast_pairing.EbyKDot

end fast_pairing
