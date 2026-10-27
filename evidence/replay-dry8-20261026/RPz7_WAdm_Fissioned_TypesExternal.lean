import RPz7_WAdm_Carrier
set_option autoImplicit false
namespace WAdm_Fissioned
/-- Content carrier of the owned standard array iterator. Native library
validity/lifetime and allocator behavior remain external runtime trust. -/
abbrev core.array.iter.IntoIter (T : Type) (_N : Aeneas.Std.Usize) := List T
end WAdm_Fissioned
