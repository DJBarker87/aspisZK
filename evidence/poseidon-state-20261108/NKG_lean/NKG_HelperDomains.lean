import NKG_HelperCuts
set_option autoImplicit false
noncomputable section
namespace AspisR1.NKG_HelperDomains
open Aeneas Aeneas.Std Result FIq_Native
open FIv_NativeArithmetic (NQ)
open FIv_NativeValue (Canon)
open FIw_ArrayValue (canonical)
open FJh_Base (State cell P)
/-- Actual logged dot arguments inherit canonicality from SAME selector reads
and ROM entries; the seven-element length is in the carriers themselves. -/
theorem internal (s l : State) (weights : Fin 2 → NKG_HelperCuts.Seven)
 (constants : Fin 2 → NKG_HelperCuts.Constants7) (dots : Fin 2 → NQ)
 (states replies : Fin 2 → State) (factors : Fin 2 → NQ) (out : State)
 (dotCalls roundCalls : Nat) (hl : canonical l)
 (cut : NKG_HelperCuts.Internal s l weights constants dots states replies factors out dotCalls roundCalls) :
 ∀ c,canonical (weights c) ∧ ∀ i,(cell (constants c) i).val<P := by
 intro c
 constructor
 · intro x hx
   obtain ⟨j,hj,rfl⟩ := List.getElem_of_mem hx
   have h7 : j<(7#usize).val := by simpa only [(weights c).property] using hj
   change Canon (cell (weights c) ⟨j,h7⟩)
   rw [cut.weightArgs]
   exact hl _ (List.getElem_mem _)
 · intro i
   rw [cut.constantArgs]
   exact FJh_InternalConstants.canonical _
/-- Both actual column calls establish the CLOSED column packet's domain on
these three weights and all six original ROM columns, with no caller success. -/
theorem full (s l : State) (weights : Fin 2 → Array NQ 3#usize)
 (columns : Fin 2 → Fin 3 → Array U32 16#usize) (replies states constants : Fin 2 → State)
 (middle : State) (packed out : NKG_HelperCuts.Packed) (columnCalls roundCalls : Nat)
 (hl : canonical l)
 (cut : NKG_HelperCuts.Full s l weights columns replies states constants middle packed out columnCalls roundCalls) :
 ∀ c,canonical (weights c) ∧ ∀ i k,(cell (columns c i) k).val<P := by
 intro c
 constructor
 · intro x hx
   obtain ⟨j,hj,rfl⟩ := List.getElem_of_mem hx
   have h3 : j<(3#usize).val := by simpa only [(weights c).property] using hj
   change Canon (cell (weights c) ⟨j,h3⟩)
   rw [cut.weightArgs]
   exact hl _ (List.getElem_mem _)
 · intro i k
   rw [cut.constantArgs]
   split
   · exact FJb_InitialConstants.bounded _ k
   · exact FJe_FinalConstants.bounded _ k
#print internal
#print axioms internal
#print full
#print axioms full
end AspisR1.NKG_HelperDomains
end
