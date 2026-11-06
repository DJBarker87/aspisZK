import NJL_AbsorptionPrologue
import NJL_Traverse
set_option autoImplicit false
noncomputable section
namespace AspisR1.NJL_AbsorptionInvocation
open Aeneas Aeneas.Std Result
open FIv_NativeArithmetic (NQ)
open FIv_NativeValue (Canon)
open NJB_AbsorptionScales (Scale)
def indices : List (Fin 16) := List.ofFn (fun i : Fin 16=>i)
/-- Exact native one-lane cut paired with its SAME actual complete child Result.
There is no mutable footprint in this returning scalar call. -/
def Lane (scales : Fin 3 → Scale) (opened : Fin 16 → NQ) (i : Fin 16) (reply : NQ) : Prop :=
 NJB_AbsorptionLane.reference scales opened i=ok reply ∧
 NJB_AbsorptionCuts.lane (fun j=>(scales j).cache) opened i reply reply
  (scales (NJB_AbsorptionLane.group i)).cache (opened i) 3 1
/-- All sixteen lane cuts instantiated with actual full-carrier prepared
Results; no binary-bit or independent-cache premise. The generic traversal's
child interface is discharged internally here. -/
theorem lanes (scales : Fin 3 → Scale) (opened : Fin 16 → NQ)
 (prepared : ∀ j,Canon (scales j).value ∧ NJB_PreparedLaws.Domain (scales j).cache (scales j).value)
 (canonical : ∀ j,Canon (opened j)) :
 ∃ ys,NJB_Traverse.run (NJB_AbsorptionLane.reference scales opened) indices=ok ys ∧
 (∀ y∈ys.val,Canon y) ∧ List.Forall₂ (Lane scales opened) indices ys.val := by
 apply NJL_Traverse.packet
 intro i _
 obtain ⟨reply,call,hr,_⟩ := NJB_AbsorptionLane.result scales opened i prepared canonical
 exact ⟨reply,call,hr,call,rfl,rfl,rfl,rfl,rfl⟩
/-- Positive full-array root with complete native prologue, every ordered
lane cut, cache domains and the exact adopted cohort Result. Only SAME input
canonicality remains. Native initialization/array construction/control still
requires the register's structural certificate; this statement does not
silently assert any missing observation. -/
theorem source (low fixed two eight nodes : NQ) (opened : Array NQ 16#usize)
 (hl : Canon low) (hf : Canon fixed) (ht : Canon two) (he : Canon eight) (hn : Canon nodes)
 (ho : FIw_ArrayValue.canonical opened) :
 ∃ r p scales (ys : {ys : List NQ // ys.length=indices.length}) (out : Array NQ 16#usize),
 NJL_AbsorptionPrologue.Cut ![low,fixed,two,eight,nodes] r p
  (fun j=>⟨NJL_AbsorptionPrologue.kind j,
   NJL_AbsorptionPrologue.left ![low,fixed,two,eight,nodes] r j,
   NJL_AbsorptionPrologue.right ![low,fixed,two,eight,nodes] r j⟩)
  (fun j=>r (NJL_AbsorptionPrologue.replyIndex j)) NJL_AbsorptionPrologue.positions p p 7 3 ∧
 NJL_AbsorptionPrologue.Clauses ![low,fixed,two,eight,nodes] r p ∧
 List.Forall₂ (Lane scales (NJB_Absorption.cell opened)) indices ys.val ∧
 out.val=ys.val ∧ FIw_ArrayValue.canonical out ∧
 NJB_Absorption.reference low fixed two eight nodes opened=ok out ∧
 FIq_Native.pool_v1.pair_forest_semantic_terminal.absorption_lanes_literal low fixed two eight nodes opened=ok out := by
 obtain ⟨r,p,scales,cut,clauses,scaleCall,domain⟩ := NJL_AbsorptionPrologue.source low fixed two eight nodes hl hf ht he hn
 obtain ⟨ys,run,hys,trace⟩ := lanes scales (NJB_Absorption.cell opened)
  (fun j=>⟨(domain j).2.2.1,(domain j).2.2.2⟩)
  (fun j=>ho _ (List.getElem_mem _))
 let out : Array NQ 16#usize := Array.make 16#usize ys.val
  (by simpa only [indices,List.length_ofFn,NJB_Absorption.size] using ys.property)
 have reference : NJB_Absorption.reference low fixed two eight nodes opened=ok out := by
  simp only [NJB_Absorption.reference,scaleCall,bind_tc_ok]
  change (do let ys ← NJB_Traverse.run (NJB_AbsorptionLane.reference scales (NJB_Absorption.cell opened)) indices
             ok (Array.make 16#usize ys.val _))=ok out
  rw [run]
  rfl
 exact ⟨r,p,scales,ys,out,cut,clauses,trace,rfl,hys,reference,
  (NJB_AbsorptionAssociation.result low fixed two eight nodes opened hl hf ht he hn ho).symm.trans reference⟩
#print source
#print axioms lanes
#print axioms source
end AspisR1.NJL_AbsorptionInvocation
end
