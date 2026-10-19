import AspisR1HeapFilled.Types
import AspisR1HeapFilledOverwrite.TypesExternal

namespace AspisR1HeapFilledOverwrite

abbrev aspis_core.r0.Error := AspisR1HeapFilled.aspis_core.r0.Error
abbrev aspis_core.r0.Error.Allocation := AspisR1HeapFilled.aspis_core.r0.Error.Allocation

/-- The helper's generated closure is only the mapped error value. Its Error
    type and shared Aeneas representation owners are reused from the pinned
    accepted heap extraction, avoiding a second discriminant instance. -/
@[reducible]
def aspis_core.r0.heap.filled_overwrite.closure (T : Type) := Unit

end AspisR1HeapFilledOverwrite
