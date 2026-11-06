import NJB_PatternReference
set_option autoImplicit false
noncomputable section
namespace AspisR1.NJB_PatternArray
open Aeneas Aeneas.Std Result
open FIv_NativeArithmetic (NQ)
open FIv_NativeValue (Canon decode)
theorem size4 : (4#usize).val=4 := by scalar_tac
theorem size14 : (14#usize).val=14 := by scalar_tac
theorem size26 : (26#usize).val=26 := by scalar_tac
def state (a : Array NQ 4#usize) (i : Fin 4) : NQ :=
 NJB_ArrayCarrier.cell a (Fin.cast size4.symm i)
def patterns (a : Array NQ 14#usize) (i : Fin 14) : NQ :=
 NJB_ArrayCarrier.cell a (Fin.cast size14.symm i)
def selectors (a : Array NQ 26#usize) (i : Fin 26) : NQ :=
 NJB_ArrayCarrier.cell a (Fin.cast size26.symm i)
def pack (s : Fin 4 → NQ) : Array NQ 4#usize :=
 NJB_ArrayCarrier.array (fun i=>s (Fin.cast size4 i))
theorem state_pack (s : Fin 4 → NQ) : state (pack s)=s := by
 funext i
 simp only [state,pack,NJB_ArrayCarrier.cell_array]
 exact congrArg s (Fin.ext rfl)
def reference (values : Array NQ 4#usize) (weights : Array NQ 26#usize) (terms : Array NQ 14#usize) :
 Result (Array NQ 4#usize) := do
 let out ← NJB_PatternReference.reference (patterns terms) (selectors weights) (state values)
 ok (pack out)
/-- Full four-word-record array Result and complete mutable-value frame. The
three inputs are the SAME arrays, not independently decoded witnesses. -/
theorem result (values : Array NQ 4#usize) (weights : Array NQ 26#usize) (terms : Array NQ 14#usize)
 (hv : FIw_ArrayValue.canonical values) (hw : FIw_ArrayValue.canonical weights)
 (ht : FIw_ArrayValue.canonical terms) :
 ∃ out,reference values weights terms=ok out ∧ FIw_ArrayValue.canonical out ∧
 (fun i=>decode (state out i))=NJB_PatternReference.model
  (fun i=>decode (patterns terms i)) (fun i=>decode (selectors weights i)) (fun i=>decode (state values i)) := by
 obtain ⟨out,call,ho,vo⟩ := NJB_PatternReference.result (patterns terms) (selectors weights) (state values)
  (fun i=>NJB_ArrayCarrier.canonical_cell terms ht _) (fun i=>NJB_ArrayCarrier.canonical_cell weights hw _)
  (fun i=>NJB_ArrayCarrier.canonical_cell values hv _)
 refine ⟨pack out,?_,?_,?_⟩
 · simp only [reference,call,bind_tc_ok]
 · exact NJB_ArrayCarrier.canonical_array _ (fun i=>ho _)
 · rw [state_pack]
   exact vo
#print result
#print axioms size4
#print axioms size14
#print axioms size26
#print axioms state_pack
#print axioms result
end AspisR1.NJB_PatternArray
end
