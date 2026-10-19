import CuSavingsTryGraphRuntime

/-! Concrete initialized/uninitialized storage interpretation. Rust primitive
and experimental frontend admission remain separate obligations. -/
namespace AspisR1CuArrayGraph
abbrev core.mem.maybe_uninit.MaybeUninit (T : Type) := Option T
#print axioms core.mem.maybe_uninit.MaybeUninit
end AspisR1CuArrayGraph
