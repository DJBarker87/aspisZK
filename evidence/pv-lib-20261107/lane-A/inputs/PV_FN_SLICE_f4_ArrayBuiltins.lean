import PV_FN_SLICE_f4_Repeat
import PV_STX2_SliceCompleteAggregates
set_option autoImplicit false
noncomputable section
namespace PV_FN_SLICE_f4_ArrayBuiltins
open Aeneas Aeneas.Std PV_STX_Machine PV_STX2_Syntax PV_STX2_Store PV_STX2_SliceMachine PV_EVHB_OwnerMachine
abbrev Handler (E : Type) := PV_STX2_Native.Request Data → OWNER → Reply OWNER E Data

/-- Existing compiler-builtin interpreter, named structurally. Other requests
retain the entire backend reply domain. This installs no new success callback. -/
def Spec {E : Type} (H : Handler E) : Prop := ∃ backend : Handler E,
  H = PV_STX2_SliceArrayInterpretation.handler (PV_STX2_SliceDriverArrays.handler backend)

theorem original {E : Type} (backend : Handler E) :
    Spec (PV_STX2_SliceArrayInterpretation.handler (PV_STX2_SliceDriverArrays.handler backend)) :=
  ⟨backend,rfl⟩

/-- Source57's exact pure ArrayRepeat operation, from the existing source
builtin theorem. It copies the uninitialized UNION CARRIER, never its payload. -/
theorem repeat_reply {E : Type} (H : Handler E) (spec : Spec H) (a : Nat) (v : Data) (w : OWNER) :
    H (.child PV_FN_SLICE_f4_Repeat.source.2.1 a [v]) w =
      ⟨.returned (.ok (.array (List.replicate 16 v))),w,[]⟩ := by
  obtain ⟨backend,rfl⟩ := spec
  exact PV_STX2_SliceDriverArrays.repeat_outer_reply backend a v w

/-- The emitted mutable-array-to-slice builtin preserves the backing selected
by f4's own borrow and adds its source length. No pointer value is chosen. -/
theorem mutable {E : Type} (H : Handler E) (spec : Spec H)
    (a : Nat) (p : Address) (m : Data) (w : OWNER) :
    H (.child PV_STX2_SliceDriverArrays.mutableCallee a
      [PV_STX2_TypedReferences.reference p m]) w =
      ⟨.returned (.ok (PV_STX2_TypedReferences.reference p (.number 16))),w,[]⟩ := by
  obtain ⟨backend,rfl⟩ := spec
  exact PV_STX2_SliceDriverArrays.mutable_outer_reply backend a p m w

/-- Source dispatch recognizes both compiler builtins as native children. -/
theorem repeat_dispatch : PV_STX2_SlicePrograms.dispatch PV_FN_SLICE_f4_Repeat.source.2.1 = none := rfl

theorem mutable_dispatch : PV_STX2_SlicePrograms.dispatch PV_STX2_SliceDriverArrays.mutableCallee = none := rfl

/-- The initialized logical carrier has precisely the source bound and every
slot is the same MaybeUninit union representation constructed by CLOSED f23. -/
theorem repeat_slot (i : Nat) (bound : i < 16) :
    (List.replicate 16 PV_FN_SLICE_f23.value)[i]? = some PV_FN_SLICE_f23.value := by
  simp only [List.getElem?_replicate,if_pos bound]

#print axioms original
#print axioms repeat_reply
#print axioms mutable
#print axioms repeat_dispatch
#print axioms mutable_dispatch
#print axioms repeat_slot
end PV_FN_SLICE_f4_ArrayBuiltins
