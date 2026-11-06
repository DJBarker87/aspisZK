import NIH_SelectorRow
import NJB_ArrayCarrier
set_option autoImplicit false
noncomputable section
namespace AspisR1.NKI_SelectorWindow
open Aeneas Aeneas.Std Result
open FIv_NativeArithmetic (NQ)
abbrev Selectors := FIq_Native.pool_v1.pair_forest_copy_terminal.Selectors
def project (s : Selectors) (hi : Fin 64) (lo : Fin 16) : NQ × NQ :=
 (NJB_ArrayCarrier.cell s.high hi,NJB_ArrayCarrier.cell s.low lo)
def representative (s : Selectors) (hi : Fin 64) (lo : Fin 16) : Selectors :=
 ⟨NJB_ArrayCarrier.array (N:=64#usize) (fun i=>if i=hi then (project s hi lo).1 else FIq_Native.field.QM31.ZERO),
  NJB_ArrayCarrier.array (N:=16#usize) (fun i=>if i=lo then (project s hi lo).2 else FIq_Native.field.QM31.ZERO)⟩
/-- The changed K003/K004 harness shape uses one arbitrary receiver window.
This frame law lifts its exact footprint to any full receiver: unobserved
coordinates do not occur in the cut, not a zero-input domain restriction. -/
theorem projection (s : Selectors) (hi : Fin 64) (lo : Fin 16) :
 project (representative s hi lo) hi lo=project s hi lo := by
 simp only [project,representative,NJB_ArrayCarrier.cell_array,if_true]
def viewLog (s : Selectors) (hi : Fin 64) (lo : Fin 16) : Fin 3 → NQ × NQ := fun _=>project s hi lo
theorem frame (s t : Selectors) (hi : Fin 64) (lo : Fin 16) (same : project s hi lo=project t hi lo) :
 viewLog s hi lo=viewLog t hi lo := by
 funext i
 exact same
theorem source (s : Selectors) (hi : Fin 64) (lo : Fin 16) :
 viewLog (representative s hi lo) hi lo=viewLog s hi lo := frame _ _ hi lo (projection s hi lo)
#print axioms projection
#print axioms frame
#print axioms source
end AspisR1.NKI_SelectorWindow
end
