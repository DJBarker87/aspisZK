import EmptyRootSource

/-! The actual empty-root helper is a checked table read followed by mapping
its exact identity constructor. No field normalization is required. -/
set_option autoImplicit false
namespace AspisR1.EmptyRootExecution
open Aeneas Aeneas.Std Result WP
open AspisR1SelectedMaskProbe
open AspisV8R19.TraversalRuntime
abbrev table := AspisR1EmptyRootCandidate.pool_v1.pair_forest_semantic_terminal.constants.POOL_V1_PAIR_EMPTY_ROOTS_V1
abbrev ctor := AspisR1EmptyRootCandidate.field.M31_constructor
abbrev source := AspisR1EmptyRootCandidate.pool_v1.pair_forest_semantic_terminal.empty_root

theorem mapState_ctor (xs : List U32) :
    mapState (BuiltinFnMut U32 field.M31).call_mut xs ctor = .ok (xs, ctor) := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    have hcall : ∀ y : U32, (BuiltinFnMut U32 field.M31).call_mut ctor y = .ok (y, ctor) := by
      intro y
      rfl
    simp only [mapState, hcall, bind_tc_ok, ih]

theorem map_ctor_identity {N : Usize} (a : Array U32 N) :
    core.array.Array.map (BuiltinFnMut U32 field.M31) a ctor = .ok a := by
  exact core.array.Array.map_success (BuiltinFnMut U32 field.M31) a ctor a.val ctor (mapState_ctor a.val)

def row (level : Usize) (hlevel : level.val < 21) : Array field.M31 8#usize :=
  table.val[level.val]'(by simpa [table.property] using hlevel)

theorem source_success (level : Usize) (hlevel : level.val < 21) :
    source level = .ok (row level hlevel) := by
  have hbound : level.val < table.length := by simpa [table.property] using hlevel
  obtain ⟨a, hread, hvalue⟩ := WP.spec_imp_exists (Array.index_usize_spec table level hbound)
  have ha : a = row level hlevel := by simpa only [row] using hvalue
  simp only [source, AspisR1EmptyRootCandidate.pool_v1.pair_forest_semantic_terminal.empty_root,
    hread, bind_tc_ok, map_ctor_identity]
  exact congrArg Result.ok ha

#print axioms mapState_ctor
#print axioms map_ctor_identity
#print axioms source_success
end AspisR1.EmptyRootExecution
