import PV_LIB_A_DropInPlace248
import PV_LIB_A_GenericDropBinding
import PV_LIB_A_CellSetMetadata
set_option autoImplicit false
namespace PV_LIB_A_TypedBindingFacts
open PV_STX2_Syntax PV_LIB_A_CellSetBegin PV_LIB_A_TypedDestruct

def empty : Generics := ⟨[],[],[],[]⟩
def hooksType : Data := .object [("Adt",.object [("id",.object [("Adt",.number 142)]),
  ("generics",encode empty)])]
def arcType (ty : Data) : Data := .object [("Adt",.object [("id",.object [("Adt",.number 21)]),
  ("generics",encode ⟨[],[ty],[],[]⟩)])]
def untracked (ty : Data) : Data := .object
  [("kind",.object [("BuiltinOrAuto",.object [("builtin_data",.atom "UntrackedDestruct"),
    ("parent_trait_refs",.array []),("types",.array [])])]),
   ("trait_decl_ref",.object [("regions",.array []),("skip_binder",.object
     [("id",.number 5),("generics",encode ⟨[],[ty],[],[]⟩)])])]

theorem hooks_method : PV_LIB_A_ExactDestructMethods.byType hooksType =
    some (.call (fnPtr 608 ⟨[.atom "Erased"],[],[],[]⟩)) := rfl

/-- An actual typed248 specialization, including its UntrackedDestruct witness,
is resolved to SpawnHooks glue. The witness does not turn destruction into noop. -/
theorem typed248_hooks :
    PV_LIB_A_DropInPlace248.resolution (.object [("Regular",
      fnPtr 248 ⟨[],[hooksType],[],[untracked hooksType]⟩)]) =
      some (.call (fnPtr 608 ⟨[.atom "Erased"],[],[],[]⟩)) := rfl

/-- Checked metadata gap: the retained Arc type has one type argument, but
method405's generic template contains both Free0 and Free1. A resolver cannot
bind the latter from this type alone. No claim about Rust failing to drop Arc. -/
theorem arc_allocator_unbound (ty : Data) :
    PV_LIB_A_ExactDestructMethods.byType (arcType ty) = none := rfl

theorem no_selected_arc_glue (ty fn : Data) :
    PV_LIB_A_ExactDestructMethods.byType (arcType ty) ≠ some (.call fn) := by
  rw [arc_allocator_unbound]
  intro h
  cases h

/-- The translator's explicit allocator-erasure marker is not an empty type. -/
theorem erased_allocator_not_noop :
    PV_LIB_A_ExactDestructMethods.byType
      (.object [("Error",.atom "removed allocator parameter")]) = none := rfl

/-- Passing two actual type arguments does specialize the whole drop_slow
program. There is no raw generic body substituted for the instantiated body. -/
theorem slow_specialized (payload allocator : Data) :
    PV_LIB_A_GenericDropBinding.bind 584 ⟨[],[payload,allocator],[],[]⟩ =
      some (PV_LIB_A_TypedBody584.program [payload,allocator]) := rfl

#print axioms empty
#print axioms hooksType
#print axioms arcType
#print axioms untracked
#print axioms hooks_method
#print axioms typed248_hooks
#print axioms arc_allocator_unbound
#print axioms no_selected_arc_glue
#print axioms erased_allocator_not_noop
#print axioms slow_specialized
end PV_LIB_A_TypedBindingFacts
