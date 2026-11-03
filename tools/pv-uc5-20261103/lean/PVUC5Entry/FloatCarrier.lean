import Aeneas

namespace PV_UC5_Entry
-- Bit-pattern carrier for the opaque native Duration -> f64 -> JSON boundary.
-- No Lean floating-point computation or equality-to-native law is asserted.
abbrev F64 := Aeneas.Std.U64
end PV_UC5_Entry
