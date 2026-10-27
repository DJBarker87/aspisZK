import R1Z.PV_Src_PortConstantTraces
import R1Z.PV_Src_PortEnumerateValues
import R1Z.PV_Src_PortInitialConstants
import R1Z.PV_Src_PortFinalConstants
import R1Z.PV_Src_PortInternalConstants

/-! The actual frozen constant groups instantiate the symbolic round loops.
No iterator or constant-canonicality premise remains in these three equations.
All callback Results remain explicit. This is not a full parent refinement. -/
set_option autoImplicit false
namespace R1Z.PV_Src_PortConstantInstance
open Aeneas Aeneas.Std Result R0Z.WriterRefine
open BuilderForestStdPort BuilderForestAdmissionPort PV_Src_PortSboxStep PV_Src_PortTraceRounds

theorem initial (p : Usize × State)
    (hp : p ∈ PV_Src_PortEnumerateTrace.pairs poseidon2.EXTERNAL_INITIAL.val 0#usize) : Canonical p.2 := by
  have hx := PV_Src_PortEnumerateValues.values _ _ p hp
  obtain ⟨i,hi,he⟩ := List.mem_iff_getElem.mp hx
  have hlt : i<4 := by simpa only [poseidon2.EXTERNAL_INITIAL.property,UScalar.ofNatCore_val_eq] using hi
  have hv := PV_Src_PortInitialConstants.canonical ⟨i,hlt⟩
  simpa only [getElem!_pos poseidon2.EXTERNAL_INITIAL.val i hi,he] using hv

theorem final_round (p : Usize × State)
    (hp : p ∈ PV_Src_PortEnumerateTrace.pairs poseidon2.EXTERNAL_FINAL.val 0#usize) : Canonical p.2 := by
  have hx := PV_Src_PortEnumerateValues.values _ _ p hp
  obtain ⟨i,hi,he⟩ := List.mem_iff_getElem.mp hx
  have hlt : i<4 := by simpa only [poseidon2.EXTERNAL_FINAL.property,UScalar.ofNatCore_val_eq] using hi
  have hv := PV_Src_PortFinalConstants.canonical ⟨i,hlt⟩
  simpa only [getElem!_pos poseidon2.EXTERNAL_FINAL.val i hi,he] using hv

theorem internal (p : Usize × U32)
    (hp : p ∈ PV_Src_PortEnumerateTrace.pairs poseidon2.INTERNAL.val 0#usize) : p.2.val < 2147483647 := by
  have hx := PV_Src_PortEnumerateValues.values _ _ p hp
  obtain ⟨i,hi,he⟩ := List.mem_iff_getElem.mp hx
  have hlt : i<14 := by simpa only [poseidon2.INTERNAL.property,UScalar.ofNatCore_val_eq] using hi
  have hv := PV_Src_PortInternalConstants.canonical ⟨i,hlt⟩
  simpa only [getElem!_pos poseidon2.INTERNAL.val i hi,he] using hv

theorem initial_source {F : Type}
    (callback : core.ops.function.FnMut F poseidon2.Poseidon2RoundTransition Unit)
    (s input : State) (trace : F) (round : U8) (hs : Canonical s) :
    poseidon2.permute_optimized_with_trace_loop0
      (sourceExternalLinear := PV_Src_ExternalReference.dictionary) callback
      ⟨⟨Array.to_slice poseidon2.EXTERNAL_INITIAL,0⟩,0#usize⟩ s trace round input =
    fullSteps callback (fun i => poseidon2.Poseidon2RoundKind.ExternalInitial (UScalar.cast .U8 i))
      (PV_Src_PortEnumerateTrace.pairs poseidon2.EXTERNAL_INITIAL.val 0#usize) s trace round input :=
  PV_Src_PortInitialRounds.source callback _ _ PV_Src_PortConstantTraces.initial
    s input trace round hs initial

theorem internal_source {F : Type}
    (callback : core.ops.function.FnMut F poseidon2.Poseidon2RoundTransition Unit)
    (s input : State) (trace : F) (round : U8) (hs : Canonical s) :
    poseidon2.permute_optimized_with_trace_loop1 callback
      ⟨poseidon2.INTERNAL.val,0#usize⟩ s trace round input =
    PV_Src_PortInternalRounds.steps callback
      (PV_Src_PortEnumerateTrace.pairs poseidon2.INTERNAL.val 0#usize) s trace round input :=
  PV_Src_PortInternalRounds.source callback _ _ PV_Src_PortConstantTraces.internal
    s input trace round hs internal

theorem final_source {F : Type}
    (callback : core.ops.function.FnMut F poseidon2.Poseidon2RoundTransition Unit)
    (s input : State) (trace : F) (round : U8) (hs : Canonical s) :
    poseidon2.permute_optimized_with_trace_loop2
      (sourceExternalLinear := PV_Src_ExternalReference.dictionary) callback
      ⟨⟨Array.to_slice poseidon2.EXTERNAL_FINAL,0⟩,0#usize⟩ s trace round input =
    PV_Src_PortFinalRounds.result (fullSteps callback
      (fun i => poseidon2.Poseidon2RoundKind.ExternalFinal (UScalar.cast .U8 i))
      (PV_Src_PortEnumerateTrace.pairs poseidon2.EXTERNAL_FINAL.val 0#usize) s trace round input) :=
  PV_Src_PortFinalRounds.source callback _ _ PV_Src_PortConstantTraces.final_round
    s input trace round hs final_round

#print axioms initial
#print axioms final_round
#print axioms internal
#print axioms initial_source
#print axioms internal_source
#print axioms final_source
end R1Z.PV_Src_PortConstantInstance
