import PV_LIB_SPEC_Native13
set_option autoImplicit false
noncomputable section
namespace PV_LIB_SPEC_ArcPhysicalGap13
open PV_STX_Machine PV_STX2_Syntax PV_STX2_Store PV_STX2_SliceMachine
open PV_EVHB_OwnerMachine PV_LIB_SPEC_D984 PV_LIB_SPEC_Frozen

/-- SPEC-C11: the current assembled non-allocation clone branch discards all
physical heap changes even if its lower native reply had them. This covers
its successful decoded Arc branch for ANY source/world/operand/physical base;
it is not an original-entry reachability assertion. -/
theorem drops_physical_write (regs : PV_LIB_SPEC_CallbackStores.Registers)
    (p : Parameters) (c : Config) (fn : Data) (a : Nat) (args : List Data)
    (w : OWNER) (raw : Reply OWNER Event Data) (ignored value : Data) (count : Nat)
    (function : PV_THR2_OffPath.functionId fn = some 360)
    (native : PV_LIB_SPEC_CallbackRuntime.native regs p c (.child fn a args) w = some raw)
    (returned : raw.answer = .returned (.ok ignored))
    (source : PV_LIB_SPEC_BoundRuntime.arc (runtime p).carrier c.store w args = some (value,count))
    (ordinary : PV_LIB_SPEC_BoundRuntime.allocationToken (.child fn a args) = false)
    (bounded : count ≤ PV_THR2_LibrarySemantics_ArcClone.maxRefcount) :
    ∃ out, PV_LIB_SPEC_CallbackRuntime.answer regs p c (.child fn a args) w = some out ∧
      out.world.world.memory = w.world.memory := by
  have branch : PV_LIB_SPEC_CallbackRuntime.valueAnswer regs p c (.child fn a args) w =
      some ⟨.returned (.ok value),w,raw.events⟩ := by
    unfold PV_LIB_SPEC_CallbackRuntime.valueAnswer
    rw [native]
    change (if PV_THR2_OffPath.functionId fn = some 360 then
        match raw.answer with
        | .returned (.ok _) => do
          let (value,count) ← PV_LIB_SPEC_BoundRuntime.arc (runtime p).carrier c.store w args
          if count > PV_THR2_LibrarySemantics_ArcClone.maxRefcount then
            some (⟨.fault .abort,w,raw.events⟩ : Reply OWNER Event Data)
          else some ⟨.returned (.ok value),w,raw.events⟩
        | _ => some raw
      else if PV_LIB_SPEC_CallbackRuntime.invalidPure p c w then none else some raw) = _
    simp only [function,ite_true,returned,source,Bind.bind,Option.bind_some,
      Pure.pure,if_neg (Nat.not_lt.mpr bounded)]
  refine ⟨PV_LIB_SPEC_BoundRuntime.frameReply (.child fn a args) w
    ⟨.returned (.ok value),w,raw.events⟩,?_,?_⟩
  · unfold PV_LIB_SPEC_CallbackRuntime.answer
    rw [branch]
    rfl
  · simp only [PV_LIB_SPEC_BoundRuntime.frameReply,ordinary,Bool.false_eq_true,if_false]

/-- Byte0 is enough to distinguish an initially-one qword from the adopted
binary e05bc increment to2. No equality of whole stores/counters is needed. -/
theorem byte_conflict (memory : Nat → Option Nat) (base : Nat)
    (before : memory base = some 1) :
    memory base ≠ some 2 := by rw [before]; decide

#print axioms drops_physical_write
#print axioms byte_conflict
end PV_LIB_SPEC_ArcPhysicalGap13
